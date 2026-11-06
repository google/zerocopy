(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A relational model of programs (in a general sense) and Hoare-type rules. *)
(*                                                                           *)
(* We use a relation "R:S->S->bool" to model a program with state space S,   *)
(* where "R s s'" means "starting in s it is possible to reach s'". This is  *)
(* mainly intended for a "single-step" setting but that single step may be   *)
(* decomposed by relational decomposition into smaller steps. Hence we build *)
(* in the possibility of nondeterminism (e.g. that some flags are undefined) *)
(* from the outset, even if in common special cases R is functional.         *)
(* ========================================================================= *)

needs "Library/rstc.ml";;
needs "common/components.ml";;

(* ------------------------------------------------------------------------- *)
(* Composition of relations, which essentially stands for sequencing.        *)
(* ------------------------------------------------------------------------- *)

parse_as_infix(",,",(13,"right"));;

let seq = new_definition
 `((r1:B->C->bool) ,, r2) = \s0 s2:A. ?s1. r1 s0 s1 /\ r2 s1 s2`;;

let SEQ_ASSOC = prove
 (`forall (r1:A->B->bool) (r2:B->C->bool) (r3:C->D->bool).
    r1 ,, (r2 ,, r3) = (r1 ,, r2) ,, r3`,
  REWRITE_TAC[FUN_EQ_THM; seq] THEN MESON_TAC[]);;

let SEQ_ID = prove
 (`(forall (r:A->B->bool). (=) ,, r = r) /\
   (forall (r:A->B->bool). r ,, (=) = r)`,
  REWRITE_TAC[FUN_EQ_THM; seq] THEN MESON_TAC[]);;

let SEQ_TRIVIAL = prove
  (`((\a:A b:B. T) ,, (\a:B b:C. T)) = (\a:A b:C. T)`,
   REWRITE_TAC [FUN_EQ_THM; seq]);;

let SEQ_PRESERVES_COMPONENT = prove
 (`!c:(S,A)component R T s s'.
      (!u v. R u v ==> read c v = read c u) /\
      (!u v. T u v ==> read c v = read c u) /\
      (R ,, T) s s'
      ==> read c s' = read c s`,
  REWRITE_TAC[seq] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Subsumption of relations, basically just curried subset                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("subsumed",(12,"right"));;

let subsumed = new_definition
 `(R:A->B->bool) subsumed R' <=> !x y. R x y ==> R' x y`;;

let SUBSUMED_SEQ = prove
 (`forall (C1:A->B->bool) (C2:B->C->bool) D1 D2.
        C1 subsumed D1 /\ C2 subsumed D2
        ==> (C1 ,, C2) subsumed (D1 ,, D2)`,
  REWRITE_TAC[subsumed; seq] THEN MESON_TAC[]);;

let SUBSUMED_FOR_SEQ = prove
 (`forall (C1:A->A->bool) C2 D.
        D ,, D = D /\
        C1 subsumed D /\
        C2 subsumed D
        ==>  (C1 ,, C2) subsumed D`,
  REWRITE_TAC[FUN_EQ_THM; seq; subsumed] THEN MESON_TAC[]);;

let SUBSUMED_ID_SEQ = prove
 (`forall (R:A->A->bool) R'.
    (=) subsumed R /\ (=) subsumed R' ==> (=) subsumed (R ,, R')`,
  REWRITE_TAC[subsumed; seq] THEN MESON_TAC[]);;

let SUBSUMED_REFL = prove
 (`forall (R:A->B->bool). R subsumed R`,
  REWRITE_TAC[subsumed] THEN MESON_TAC[]);;

let SUBSUMED_SEQ_LEFT = prove
 (`forall (C:A->B->bool) D1 D2.
     C subsumed D1 /\ (=) subsumed D2
     ==> C subsumed (D1 ,, D2)`,
  REWRITE_TAC[FUN_EQ_THM; seq; subsumed] THEN MESON_TAC[]);;

let SUBSUMED_SEQ_RIGHT = prove
 (`forall (C:A->B->bool) D1 D2.
     (=) subsumed D1 /\ C subsumed D2
     ==> C subsumed (D1 ,, D2)`,
  REWRITE_TAC[FUN_EQ_THM; seq; subsumed] THEN MESON_TAC[]);;

let SUBSUMED_TRIVIAL = prove
 (`forall (R:A->B->bool). R subsumed (\s s'. true)`,
  REWRITE_TAC[subsumed] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Assignment to a state component as a (functional) relation.               *)
(* ------------------------------------------------------------------------- *)

parse_as_infix(":=",(14,"right"));;

let assign = new_definition
 `(c := y) = \(s:A) s'. write c (y:V) s = s'`;;

let SEQ = prove
 (`((c := (y:V)) ,, (r:A->B->bool)) (s:A) = r (write c y s)`,
  REWRITE_TAC[assign; seq; FUN_EQ_THM] THEN MESON_TAC[]);;

let ASSIGN_ZEROTOP_8 = prove
 (`forall c y. ((c :> zerotop_8) := y):A->A->bool = (c := word_zx y)`,
  REWRITE_TAC[assign; WRITE_ZEROTOP_8]);;

let ASSIGN_ZEROTOP_16 = prove
 (`forall c y. ((c :> zerotop_16) := y):A->A->bool = (c := word_zx y)`,
  REWRITE_TAC[assign; WRITE_ZEROTOP_16]);;

let ASSIGN_ZEROTOP_32 = prove
 (`forall c y. ((c :> zerotop_32) := y):A->A->bool = (c := word_zx y)`,
  REWRITE_TAC[assign; WRITE_ZEROTOP_32]);;

let ASSIGN_ZEROTOP_64 = prove
 (`forall c y. ((c :> zerotop_64) := y):A->A->bool = (c := word_zx y)`,
  REWRITE_TAC[assign; WRITE_ZEROTOP_64]);;

let ASSIGN_ZEROTOP_128 = prove
 (`forall c y. ((c :> zerotop_128) := y):A->A->bool = (c := word_zx y)`,
  REWRITE_TAC[assign; WRITE_ZEROTOP_128]);;

let ASSIGN_ZEROTOP_256 = prove
 (`forall c y. ((c :> zerotop_256) := y):A->A->bool = (c := word_zx y)`,
  REWRITE_TAC[assign; WRITE_ZEROTOP_256]);;

(* ------------------------------------------------------------------------- *)
(* A nondeterministic assignment of a state component.                       *)
(* ------------------------------------------------------------------------- *)

let ASSIGNS = new_definition
 `ASSIGNS (c:(A,B)component) s s' <=> exists y. (c := y) s s'`;;

let ASSIGNS_THM = prove
 (`ASSIGNS c = \(s:A) s'. exists (y:V). write c y s = s'`,
  REWRITE_TAC[FUN_EQ_THM; ASSIGNS; assign]);;

let ASSIGNS_SEQ = prove
 (`(ASSIGNS c ,, (r:A->B->bool)) = \(s:A) s'. exists (y:V). r (write c y s) s'`,
  REWRITE_TAC[ASSIGNS; assign; seq; FUN_EQ_THM] THEN MESON_TAC[]);;

let SUBSUMED_ID_EXTENSIONALLY_VALID_COMPONENT = prove
 (`forall c:(S,A)component.
        extensionally_valid_component c ==> (=) subsumed (ASSIGNS c)`,
  REWRITE_TAC[subsumed; ASSIGNS_THM; extensionally_valid_component] THEN
  MESON_TAC[]);;

let SUBSUMED_ASSIGNS_SUBCOMPONENTS = prove
 (`forall (c:(A,B)component) (d1:(B,C)component) (d2:(B,D)component).
    ASSIGNS d1 subsumed ASSIGNS d2
             ==> ASSIGNS (c :> d1) subsumed ASSIGNS (c :> d2)`,
  REWRITE_TAC[subsumed; ASSIGNS_THM; READ_COMPONENT_COMPOSE;
              WRITE_COMPONENT_COMPOSE] THEN
  MESON_TAC[]);;

let SUBSUMED_ASSIGNS_SUBCOMPONENT = prove
 (`forall (c:(A,B)component) (d:(B,C)component).
    ASSIGNS (c :> d) subsumed ASSIGNS c`,
  REWRITE_TAC[subsumed; ASSIGNS_THM; READ_COMPONENT_COMPOSE;
              WRITE_COMPONENT_COMPOSE] THEN
  MESON_TAC[]);;

let ASSIGNS_PULL_THM = prove
 (`((if P then ASSIGNS (c:(A,B)component) else c := y) =
    (\s s'. exists d. (c := if P then d else y) s s')) /\
   ((if P then c := y else ASSIGNS c) =
    (\s s'. exists d. (c := if P then y else d) s s')) /\
   ((if P then c := y else \s s'. exists (d:V). (c := f d s) s s') =
    \s s'. exists d. (c := (if P then y else f d s)) s s') /\
   ((if P then \s s'. exists d. (c := f d s) s s' else c := y) =
    \s s'. exists d. (c := (if P then f d s else y)) s s')`,
  REWRITE_TAC[ASSIGNS_THM; assign; FUN_EQ_THM] THEN MESON_TAC[]);;

let SEQ_PULL_THM = prove
 (`((\(s:A) (s':B). exists (y:V). Q y s s') ,, R = \s s'. exists y. (Q y ,, R) s s') /\
   (R ,, (\s s'. exists y. Q y s s') = \s s'. exists y. (R ,, Q y) s s')`,
  REWRITE_TAC[seq; FUN_EQ_THM] THEN MESON_TAC[]);;

let ASSIGNS_ASSIGN = prove
 (`ASSIGNS c = \(s:A) s'. exists (y:V). (c := y) s s'`,
  REWRITE_TAC[FUN_EQ_THM; ASSIGNS; assign] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Absorbing state component modification statements into others.            *)
(* ------------------------------------------------------------------------- *)

let ASSIGNS_ABSORB_SAME_COMPONENTS = prove
 (`forall c:(A,B)component.
        weakly_valid_component c
        ==> ASSIGNS c ,, ASSIGNS c = ASSIGNS c`,
  SIMP_TAC[ASSIGNS_SEQ; ASSIGNS_THM; weakly_valid_component]);;

let ASSIGNS_ABSORB_BITELEMENT = prove
 (`forall i.
    ASSIGNS(bitelement i:((N)word,bool)component) ,, ASSIGNS(bitelement i) =
       ASSIGNS(bitelement i)`,
  REWRITE_TAC[ASSIGNS_SEQ; ASSIGNS_THM; WRITE_WRITE_BITELEMENT]);;

let ASSIGNS_ABSORB_ENTIRETY_R = prove
 (`forall (c:(A,B)component).
        ASSIGNS c ,, ASSIGNS entirety = ASSIGNS entirety`,
  REWRITE_TAC[ASSIGNS_SEQ; ASSIGNS_THM; WRITE_ENTIRETY]);;

let ASSIGNS_ABSORB_ENTIRETY_L = prove
 (`forall (c:(A,B)component).
        extensionally_valid_component c
        ==> ASSIGNS entirety ,, ASSIGNS c = ASSIGNS entirety`,
  SIMP_TAC[FUN_EQ_THM; ASSIGNS_SEQ; ASSIGNS_THM; WRITE_ENTIRETY] THEN
  REWRITE_TAC[extensionally_valid_component] THEN MESON_TAC[]);;

let ASSIGNS_ABSORB_SUBCOMPONENT_R = prove
 (`forall (c:(A,B)component) (d:(B,C)component).
        valid_component c
        ==> ASSIGNS (c :> d) ,, ASSIGNS c = ASSIGNS c`,
  SIMP_TAC[FUN_EQ_THM; ASSIGNS_SEQ; ASSIGNS_THM; WRITE_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[valid_component] THEN MESON_TAC[]);;

let ASSIGNS_ABSORB_SUBCOMPONENT_L = prove
 (`forall (c:(A,B)component) (d:(B,C)component).
        extensionally_valid_component c /\
        extensionally_valid_component d
        ==> ASSIGNS c ,, ASSIGNS (c :> d) = ASSIGNS c`,
  SIMP_TAC[FUN_EQ_THM; ASSIGNS_SEQ; ASSIGNS_THM; WRITE_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[extensionally_valid_component] THEN MESON_TAC[]);;

let ASSIGNS_RVALUE = prove
 (`forall (y:V). ASSIGNS(rvalue y):A->A->bool = (=)`,
  REWRITE_TAC[FUN_EQ_THM; ASSIGNS_THM; READ_WRITE_RVALUE]);;

let ASSIGNS_ABSORB_RVALUE = prove
 (`(forall (c:(A,B)component) (y:V).
      ASSIGNS c ,, ASSIGNS (rvalue y) = ASSIGNS c) /\
   (forall (c:(A,B)component) (y:V).
      ASSIGNS (rvalue y) ,, ASSIGNS c = ASSIGNS c) /\
   (forall (c:(A,B)component) (d:(V,V2)component) (y:V).
      ASSIGNS c ,, ASSIGNS (rvalue y :> d ) = ASSIGNS c) /\
   (forall (c:(A,B)component) (d:(V,V2)component) (y:V).
      ASSIGNS (rvalue y :> d) ,, ASSIGNS c = ASSIGNS c)`,
  REWRITE_TAC[COMPONENT_COMPOSE_RVALUE; ASSIGNS_RVALUE] THEN
  REWRITE_TAC[SEQ_ID]);;

(* ------------------------------------------------------------------------- *)
(* Commuting state component modification statements.                        *)
(* These are uniform even in cases where there is an absorption result.      *)
(* ------------------------------------------------------------------------- *)

let ASSIGNS_SWAP_ORTHOGONAL_COMPONENTS = prove
 (`forall (c:(A,B)component) (d:(A,C)component).
        orthogonal_components c d
        ==> ASSIGNS c ,, ASSIGNS d = ASSIGNS d ,, ASSIGNS c`,
  REWRITE_TAC[orthogonal_components; seq] THEN
  REWRITE_TAC[ASSIGNS_SEQ; ASSIGNS_THM; FUN_EQ_THM] THEN
  MESON_TAC[]);;

let ASSIGNS_SWAP_ELEMENTS = prove
 (`forall i j:K. ASSIGNS (element i) ,, ASSIGNS (element j) =
           ASSIGNS (element j) ,, ASSIGNS (element i)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `i:K = j` THEN
  ASM_SIMP_TAC[ASSIGNS_ABSORB_SAME_COMPONENTS; VALID_COMPONENT_ELEMENT] THEN
  MATCH_MP_TAC ASSIGNS_SWAP_ORTHOGONAL_COMPONENTS THEN
  ASM_SIMP_TAC[ORTHOGONAL_COMPONENTS_ELEMENT]);;

let ASSIGNS_SWAP_BITELEMENTS = prove
 (`forall i j. ASSIGNS (bitelement i) ,, ASSIGNS (bitelement j) =
         ASSIGNS (bitelement j) ,, ASSIGNS (bitelement i)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `i:num = j` THEN
  ASM_REWRITE_TAC[ASSIGNS_ABSORB_BITELEMENT] THEN
  MATCH_MP_TAC ASSIGNS_SWAP_ORTHOGONAL_COMPONENTS THEN
  ASM_SIMP_TAC[ORTHOGONAL_COMPONENTS_BITELEMENT]);;

let ASSIGNS_SWAP_SUBCOMPONENTS = prove
 (`forall (c:(A,B)component) (d:(B,C)component) (d':(B,D)component).
        valid_component c /\
        ASSIGNS d ,, ASSIGNS d' = ASSIGNS d' ,, ASSIGNS d
        ==> ASSIGNS (c :> d) ,, ASSIGNS (c :> d') =
            ASSIGNS (c :> d') ,, ASSIGNS (c :> d)`,
  REWRITE_TAC[valid_component; seq; ASSIGNS; assign;
              FUN_EQ_THM; WRITE_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[UNWIND_THM1] THEN SIMP_TAC[] THEN MESON_TAC[]);;

let ASSIGNS_SWAP_SUBCOMPONENTS_L = prove
 (`forall (c:(A,B)component) (d:(B,C)component).
        valid_component c /\
        extensionally_valid_component d
        ==> ASSIGNS (c :> d) ,, ASSIGNS c =
            ASSIGNS c ,, ASSIGNS (c :> d)`,
  REPEAT STRIP_TAC THEN
  SUBST1_TAC(MESON[COMPOSE_ENTIRETY]
   `ASSIGNS (c:(A,B)component) = ASSIGNS (c :> entirety)`) THEN
  MATCH_MP_TAC ASSIGNS_SWAP_SUBCOMPONENTS THEN
  ASM_SIMP_TAC[ASSIGNS_ABSORB_ENTIRETY_R; ASSIGNS_ABSORB_ENTIRETY_L]);;

let ASSIGNS_SWAP_SUBCOMPONENTS_R = prove
 (`forall (c:(A,B)component) (d:(B,C)component).
        valid_component c /\
        extensionally_valid_component d
        ==> ASSIGNS c ,, ASSIGNS (c :> d) =
            ASSIGNS (c :> d) ,, ASSIGNS c`,
  MATCH_ACCEPT_TAC(GSYM ASSIGNS_SWAP_SUBCOMPONENTS_L));;

let ASSIGNS_BYTES = prove
 (`(forall a:A word. ASSIGNS (bytes(a,0)) = (=)) /\
   (forall (a:A word) k.
       ASSIGNS (bytes(a,SUC k)) =
       ASSIGNS (element (word_add a (word k))) ,, ASSIGNS (bytes(a,k)))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `s:A word->byte` THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `s':A word->byte` THEN
  REWRITE_TAC[ASSIGNS_SEQ; ASSIGNS_THM; bytes] THEN
  EQ_TAC THENL [MESON_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`b:byte`; `n:num`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  EXISTS_TAC `val(b:byte) * 2 EXP (8 * k) + n MOD 2 EXP (8 * k)` THEN
  ONCE_REWRITE_TAC[WRITE_BYTES_RESTRICT] THEN
  REWRITE_TAC[MOD_MULT_ADD; MOD_MOD_REFL] THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[WORD_VAL_GALOIS] THEN
  SIMP_TAC[LIMB_BOUND; MOD_LT; GSYM DIMINDEX_8] THEN
  SIMP_TAC[limb; DIMINDEX_8; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  SIMP_TAC[DIV_LT; MOD_LT_EQ; EXP_EQ_0; ARITH_EQ; ADD_CLAUSES] THEN
  MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[VAL_BOUND; GSYM DIMINDEX_8]);;

let ASSIGNS_SWAP_ELEMENT_BYTES = prove
 (`forall (a:A word) b k.
        ASSIGNS (element a) ,, ASSIGNS (bytes(b,k)) =
        ASSIGNS (bytes(b,k)) ,, ASSIGNS (element a)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[ASSIGNS_BYTES; SEQ_ID] THEN GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[SEQ_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ASSIGNS_SWAP_ELEMENTS] THEN
  ASM_REWRITE_TAC[GSYM SEQ_ASSOC]);;

let ASSIGNS_SWAP_BYTES = prove
 (`forall (a:A word) k b j.
        ASSIGNS (bytes(a,k)) ,, ASSIGNS (bytes(b,j)) =
        ASSIGNS (bytes(b,j)) ,, ASSIGNS (bytes(a,k))`,
  GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[ASSIGNS_BYTES; SEQ_ID] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM SEQ_ASSOC] THEN
  REWRITE_TAC[SEQ_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC ASSIGNS_SWAP_ELEMENT_BYTES);;

let ASSIGNS_BYTES_ASWORD = prove
 (`forall (a:A word) k.
        8 * k <= dimindex(:N)
        ==> ASSIGNS (bytes(a,k) :> (asword:(num,N word)component)) =
            ASSIGNS (bytes(a,k))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ASSIGNS_THM; WRITE_COMPONENT_COMPOSE;
              asword; write; through] THEN
  REWRITE_TAC[EXISTS_WORD] THEN ONCE_REWRITE_TAC[WRITE_BYTES_RESTRICT] THEN
  REWRITE_TAC[VAL_WORD; MOD_MOD_EXP_MIN] THEN
  ASM_REWRITE_TAC[ARITH_RULE `MIN a b = if b <= a then b else a`]);;

let ASSIGNS_BYTES8 = prove
 (`forall (a:A word). ASSIGNS (bytes8 a) = ASSIGNS(bytes(a,1))`,
  GEN_TAC THEN REWRITE_TAC[bytes8] THEN
  MATCH_MP_TAC ASSIGNS_BYTES_ASWORD THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ASSIGNS_BYTES16 = prove
 (`forall (a:A word). ASSIGNS (bytes16 a) = ASSIGNS(bytes(a,2))`,
  GEN_TAC THEN REWRITE_TAC[bytes16] THEN
  MATCH_MP_TAC ASSIGNS_BYTES_ASWORD THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ASSIGNS_BYTES32 = prove
 (`forall (a:A word). ASSIGNS (bytes32 a) = ASSIGNS(bytes(a,4))`,
  GEN_TAC THEN REWRITE_TAC[bytes32] THEN
  MATCH_MP_TAC ASSIGNS_BYTES_ASWORD THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ASSIGNS_BYTES64 = prove
 (`forall (a:A word). ASSIGNS (bytes64 a) = ASSIGNS(bytes(a,8))`,
  GEN_TAC THEN REWRITE_TAC[bytes64] THEN
  MATCH_MP_TAC ASSIGNS_BYTES_ASWORD THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ASSIGNS_BYTES128 = prove
 (`forall (a:A word). ASSIGNS (bytes128 a) = ASSIGNS(bytes(a,16))`,
  GEN_TAC THEN REWRITE_TAC[bytes128] THEN
  MATCH_MP_TAC ASSIGNS_BYTES_ASWORD THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ASSIGNS_BYTES256 = prove
 (`forall (a:A word). ASSIGNS (bytes256 a) = ASSIGNS(bytes(a,32))`,
  GEN_TAC THEN REWRITE_TAC[bytes256] THEN
  MATCH_MP_TAC ASSIGNS_BYTES_ASWORD THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let SUBSUMED_ASSIGNS_BYTES = prove
 (`forall a1 (a2:N word) k1 k2.
        contained_modulo (2 EXP dimindex(:N)) (val a1,k1) (val a2,k2)
        ==> ASSIGNS (bytes(a1,k1)) subsumed ASSIGNS (bytes(a2,k2))`,
  REWRITE_TAC[CONTAINED_MODULO_WORDWISE] THEN
  GEN_TAC THEN GEN_TAC THEN GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[ASSIGNS_BYTES; NUMSEG_CLAUSES_LT] THEN
  REWRITE_TAC[IMAGE_CLAUSES; INSERT_SUBSET] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SUBSUMED_ID_EXTENSIONALLY_VALID_COMPONENT THEN
    REWRITE_TAC[EXTENSIONALLY_VALID_COMPONENT_BYTES];
    MATCH_MP_TAC SUBSUMED_FOR_SEQ THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ASSIGNS_ABSORB_SAME_COMPONENTS THEN
      REWRITE_TAC[WEAKLY_VALID_COMPONENT_BYTES];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]);
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    POP_ASSUM_LIST(K ALL_TAC)] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`i:num`;` k2:num`] THEN
  MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[ASSIGNS_BYTES; LT] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL
   [MATCH_MP_TAC SUBSUMED_SEQ_LEFT THEN REWRITE_TAC[SUBSUMED_REFL] THEN
    MATCH_MP_TAC SUBSUMED_ID_EXTENSIONALLY_VALID_COMPONENT THEN
    REWRITE_TAC[EXTENSIONALLY_VALID_COMPONENT_BYTES];
    MATCH_MP_TAC SUBSUMED_SEQ_RIGHT THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC SUBSUMED_ID_EXTENSIONALLY_VALID_COMPONENT THEN
    REWRITE_TAC[EXTENSIONALLY_VALID_COMPONENT_ELEMENT]]);;

let ASSIGNS_BYTES_SPLIT = prove
 (`forall (a:N word) m n.
     ASSIGNS(bytes(a,m + n)) =
     ASSIGNS(bytes(a,m)) ,, ASSIGNS(bytes(word_add a (word m),n))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; ASSIGNS_BYTES; SEQ_ID] THEN
  REWRITE_TAC[SEQ_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [ASSIGNS_SWAP_ELEMENT_BYTES] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let ASSIGNS_BYTES_MONO = prove
 (`forall (a:N word) m n.
        m <= n ==> ASSIGNS(bytes(a,m)) subsumed ASSIGNS(bytes(a,n))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n:num = m + (n - m)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[ASSIGNS_BYTES_SPLIT]] THEN
  MATCH_MP_TAC SUBSUMED_SEQ_LEFT THEN REWRITE_TAC[SUBSUMED_REFL] THEN
  MATCH_MP_TAC SUBSUMED_ID_EXTENSIONALLY_VALID_COMPONENT THEN
  REWRITE_TAC[EXTENSIONALLY_VALID_COMPONENT_BYTES]);;

let ASSIGNS_BYTES_SUBSUMED_SPLIT = prove
 (`forall k n (a:N word).
     ASSIGNS(bytes(a,n)) subsumed
     ASSIGNS(bytes(a,k)) ,, ASSIGNS(bytes(word_add a (word k),n - k))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n:num <= k` THENL
   [SUBGOAL_THEN `n - k = 0` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[SUB_EQ_0]; REWRITE_TAC[ASSIGNS_BYTES]] THEN
    ASM_SIMP_TAC[SEQ_ID; ASSIGNS_BYTES_MONO];
    SUBGOAL_THEN `n:num = k + (n - k)` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    REWRITE_TAC[ASSIGNS_BYTES_SPLIT; SUBSUMED_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Using a component on a relation.                                          *)
(* ------------------------------------------------------------------------- *)

let VIA = define
  `VIA (c:(S,V)component) (R:V->V->bool) =
    \s1 s2. ?y. R (read c s1) y /\ (c := y) s1 s2`;;

let VIA_COMPOSE = prove
 (`forall c1 c2 R. VIA (c1 :> c2) R = VIA c1 (VIA c2 R)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_COMPONENT; VIA; assign;
    component_compose; read; write; o_DEF; GSYM LEFT_EXISTS_AND_THM] THEN
  REPEAT GEN_TAC THEN CONV_TAC (ONCE_DEPTH_CONV UNWIND_CONV) THEN REFL_TAC);;

let VIA_SUBSUMED_ASSIGNS = prove
 (`forall c:(S,V)component R. VIA c R subsumed ASSIGNS c`,
  REWRITE_TAC[VIA; subsumed; ASSIGNS] THEN MESON_TAC[]);;

let SUBSUMED_VIA = prove
 (`forall c:(S,V)component R S. R subsumed S ==> VIA c R subsumed VIA c S`,
  REWRITE_TAC[VIA; subsumed; ASSIGNS] THEN MESON_TAC[]);;

let VIA_ASSIGN = prove
 (`forall c:(S,V)component (y:V).
    VIA (c1:(A,B)component) (c2 := y) = (c1 :> c2 := y)`,
  REWRITE_TAC[FUN_EQ_THM; VIA; assign; WRITE_COMPONENT_COMPOSE] THEN
  REPEAT GEN_TAC THEN CONV_TAC (ONCE_DEPTH_CONV UNWIND_CONV) THEN REFL_TAC);;

let VIA_ASSIGNS = prove
 (`forall (c1:(A,B)component) (c2:(B,C)component).
    VIA c1 (ASSIGNS c2) = ASSIGNS (c1 :> c2)`,
  REWRITE_TAC[FUN_EQ_THM; VIA; ASSIGNS; GSYM VIA_ASSIGN] THEN MESON_TAC[]);;

let VIA_ENTIRETY = prove
 (`forall (c:(A,B)component). VIA c (ASSIGNS entirety) = ASSIGNS c`,
  REWRITE_TAC[VIA_ASSIGNS; COMPOSE_ENTIRETY]);;

let VIA_ID = prove
 (`forall c:(S,V)component. extensionally_valid_component c ==> VIA c (=) = (=)`,
  REWRITE_TAC[FUN_EQ_THM; VIA; assign; extensionally_valid_component] THEN
  REPEAT STRIP_TAC THEN CONV_TAC (ONCE_DEPTH_CONV UNWIND_CONV) THEN
  ASM_REWRITE_TAC[]);;

let VIA_SEQ = prove
 (`forall c:(S,V)component R1 R2. strongly_valid_component c ==>
   VIA c (R1 ,, R2) = VIA c R1 ,, VIA c R2`,
  REWRITE_TAC[FUN_EQ_THM; VIA; seq; assign; GSYM LEFT_EXISTS_AND_THM;
    strongly_valid_component] THEN
  CONV_TAC (ONCE_DEPTH_CONV UNWIND_CONV) THEN REPEAT STRIP_TAC THEN
  EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `s1:V` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `y:V`;
    MAP_EVERY EXISTS_TAC [`y':V`; `y:V`] THEN
    POP_ASSUM (fun t -> POP_ASSUM (MP_TAC o C CONJ t))] THEN
  ASM_REWRITE_TAC[]);;

let VIA_SYM = prove
 (`forall c:(S,V)component d:(S,W)component A B. orthogonal_components c d ==>
   VIA c A ,, VIA d B = VIA d B ,, VIA c A`,
  REWRITE_TAC[FUN_EQ_THM; VIA; seq; assign; orthogonal_components;
    GSYM LEFT_EXISTS_AND_THM; GSYM RIGHT_EXISTS_AND_THM] THEN
  CONV_TAC (ONCE_DEPTH_CONV UNWIND_CONV) THEN MESON_TAC[]);;

let VIA_ASSIGNS_SYM = MESON [VIA_SYM; VIA_ENTIRETY]
 `forall c:(S,V)component d:(S,W)component A. orthogonal_components c d ==>
  VIA c A ,, ASSIGNS d = ASSIGNS d ,, VIA c A`;;

let ASSIGNS_VIA_SYM = MESON [VIA_SYM; VIA_ENTIRETY]
 `forall c:(S,V)component d:(S,W)component A. orthogonal_components c d ==>
  ASSIGNS c ,, VIA d A = VIA d A ,, ASSIGNS c`;;

(* ------------------------------------------------------------------------- *)
(* Using a component on a function.                                          *)
(* ------------------------------------------------------------------------- *)

let modify = define
  `modify (c:(S,V)component) (f:V->V) =
    \s. write c (f (read c s)) s`;;

let MODIFY_COMPOSE = prove
 (`!(c:(A,B)component) (d:(B,C)component) f.
   modify (c :> d) f = modify c (modify d f)`,
  REWRITE_TAC [FUN_EQ_THM; FORALL_COMPONENT; read; write; modify;
    component_compose; o_DEF]);;

let MODIFY_CONST = prove
  (`!c:(S,V)component y. modify c (\x. y) = write c y`,
   REWRITE_TAC [modify; ETA_AX]);;

let WRITE_COMPOSE = prove
  (`!(c:(A,B)component) (d:(B,C)component) x.
    write (c :> d) x = modify c (write d x)`,
    REWRITE_TAC [FUN_EQ_THM; modify; WRITE_COMPONENT_COMPOSE]);;

let MODIFY_VIA = prove
  (`!(c:(S,V)component) f s s'.
    modify c f s = s' <=> VIA c (\a a'. f a = a') s s'`,
    REWRITE_TAC [modify; VIA; assign] THEN
    CONV_TAC (ONCE_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[]);;

let MODIFY_ID = prove
 (`!c:(S,V)component. extensionally_valid_component c ==> modify c I = I`,
  REWRITE_TAC [FUN_EQ_THM; MODIFY_VIA; I_DEF; ETA_AX] THEN
  IMP_REWRITE_TAC [VIA_ID]);;

let MODIFY_o = prove
 (`!c:(S,V)component f g. strongly_valid_component c ==>
   modify c (f o g) = modify c f o modify c g`,
  REWRITE_TAC[FUN_EQ_THM; modify; o_DEF; strongly_valid_component] THEN
  CONV_TAC (ONCE_DEPTH_CONV UNWIND_CONV) THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let MODIFY_o_WRITE = prove
 (`!c:(S,V)component f x. strongly_valid_component c ==>
   modify c f o write c x = write c (f x)`,
  IMP_REWRITE_TAC [GSYM MODIFY_CONST; GSYM MODIFY_o] THEN
  REWRITE_TAC [o_DEF]);;

let WRITE_o_MODIFY = prove
 (`!c:(S,V)component x f. weakly_valid_component c ==>
   write c x o modify c f = write c x`,
  IMP_REWRITE_TAC [FUN_EQ_THM; modify; weakly_valid_component; o_DEF]);;

let MODIFY_SYM = prove
 (`!c:(S,V)component d:(S,W)component f g. orthogonal_components c d ==>
   modify c f o modify d g = modify d g o modify c f`,
  REWRITE_TAC[FUN_EQ_THM; modify; o_DEF; orthogonal_components] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let MODIFY_WRITE_SYM = prove
 (`!c:(S,V)component d:(S,W)component f x. orthogonal_components c d ==>
   modify c f o write d x = write d x o modify c f`,
  REWRITE_TAC [GSYM MODIFY_CONST] THEN MATCH_ACCEPT_TAC MODIFY_SYM);;

let WRITE_MODIFY_SYM = METIS [ORTHOGONAL_COMPONENTS_SYM; MODIFY_WRITE_SYM]
 `!c:(S,V)component d:(S,W)component f x. orthogonal_components c d ==>
  write c x o modify d f = modify d f o write c x`;;

let READ_MODIFY_VALID_COMPONENT = prove
 (`!c:(S,V)component f s. valid_component c ==>
   read c (modify c f s) = f (read c s)`,
  REWRITE_TAC [modify; valid_component] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let READ_MODIFY_ORTHOGONAL_COMPONENTS = prove
 (`forall (c:(A,B)component) (d:(A,C)component) f (s:A).
    orthogonal_components c d ==> read c (modify d f s) = read c s`,
  REWRITE_TAC[orthogonal_components; modify] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Express "a step only (possibly) changes these state components".          *)
(* ------------------------------------------------------------------------- *)

let MAYCHANGE = define
 `(MAYCHANGE:((A,B)component)list->A->A->bool) [] = (=) /\
  MAYCHANGE (CONS c cs) = ASSIGNS c ,, MAYCHANGE cs`;;

let MAYCHANGE_SING = prove
 (`forall c:(S,V)component. MAYCHANGE [c] = ASSIGNS c`,
  REWRITE_TAC[MAYCHANGE; SEQ_ID]);;

let MAYCHANGE_STARTER = prove
 (`forall s:A. (MAYCHANGE:((A,B)component)list->A->A->bool) [] s s`,
  REWRITE_TAC[MAYCHANGE]);;

let MAYCHANGE_WRITE = prove
 (`(R:A->B->bool) s0 s1 ==>
    forall c (y:V). (R ,, MAYCHANGE [c]) s0 (write c y s1)`,
  REWRITE_TAC[MAYCHANGE_SING; ASSIGNS; seq; assign] THEN MESON_TAC[]);;

let MAYCHANGE_LID = prove
 (`(MAYCHANGE:((A,B)component)list->A->A->bool) [] ,, (R:A->C->bool) = R`,
  REWRITE_TAC[MAYCHANGE; SEQ_ID]);;

let MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT = prove
 (`!c:(S,A)component cs:((S,B)component)list s s'.
      ALL (orthogonal_components c) cs /\
      MAYCHANGE cs s s'
      ==> read c s' = read c s`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[ALL; MAYCHANGE] THEN MESON_TAC[];
    FIRST_X_ASSUM(LABEL_TAC "IH") THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[ALL; MAYCHANGE; seq] THEN
    DISCH_THEN
     (CONJUNCTS_THEN2
       (CONJUNCTS_THEN2
         (LABEL_TAC "ORTHOGONAL")
         (LABEL_TAC "TAIL_ORTHOGONAL"))
       (X_CHOOSE_THEN `u:S`
         (CONJUNCTS_THEN2
           (LABEL_TAC "ASSIGNS")
           (LABEL_TAC "TAIL_MAYCHANGE")))) THEN
    SUBGOAL_THEN
     `read (c:(S,A)component) s' = read c (u:S)`
    ASSUME_TAC THENL
     [USE_THEN "IH" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `read (c:(S,A)component) (u:S) = read c s`
    ASSUME_TAC THENL
     [USE_THEN "ASSIGNS" MP_TAC THEN
      REWRITE_TAC[ASSIGNS_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:B` (SUBST1_TAC o SYM)) THEN
      MATCH_MP_TAC READ_WRITE_ORTHOGONAL_COMPONENTS THEN
      USE_THEN "ORTHOGONAL" ACCEPT_TAC;
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* This is just ASSIGNS or MAYCHANGE but with a different setting in mind.   *)
(* ------------------------------------------------------------------------- *)

let UNDEFINED_VALUE = new_definition
 `(UNDEFINED_VALUE:(A,B)component->A->A->bool) = ASSIGNS`;;

let UNDEFINED_VALUES = define
 `(UNDEFINED_VALUES:((A,B)component)list->A->A->bool) [] = (=) /\
  UNDEFINED_VALUES (CONS c cs) = ASSIGNS c ,, UNDEFINED_VALUES cs`;;

(* ------------------------------------------------------------------------- *)
(* Canonize `ASSIGNS c` term, canonizing component and scrubbing bytes_nnn   *)
(* It will not however expand "bytes_nn" nested inside :> compositions.      *)
(* ------------------------------------------------------------------------- *)

let ASSIGNS_CANON_CONV =
  let byteconv =
    GEN_REWRITE_CONV TRY_CONV
     [ASSIGNS_BYTES8; ASSIGNS_BYTES16; ASSIGNS_BYTES32; ASSIGNS_BYTES64;
      ASSIGNS_BYTES128; ASSIGNS_BYTES256] in
  fun tm ->
    match tm with
      Comb(Const("ASSIGNS",_),c) ->
       (RAND_CONV COMPONENT_CANON_CONV THENC byteconv) tm
    | _ -> failwith "ASSIGNS_CANON_CONV";;

(* ------------------------------------------------------------------------- *)
(* Compress `ASSIGNS c ,, ASSIGNS c = ASSIGNS c` for the restricted          *)
(* case of exactly the same component (not one a subcomponent).              *)
(* ------------------------------------------------------------------------- *)

let ASSIGNS_IDEMPOT_TAC =
  MATCH_MP_TAC ASSIGNS_ABSORB_SAME_COMPONENTS THEN
  CONV_TAC WEAKLY_VALID_COMPONENT_CONV;;

let ASSIGNS_IDEMPOT_CONV tm =
  let th = PART_MATCH (lhand o rand) ASSIGNS_ABSORB_SAME_COMPONENTS tm in
  MP th (WEAKLY_VALID_COMPONENT_CONV(lhand(concl th)));;

let ASSIGNS_IDEMPOT_RULE tm =
  let th = ISPEC tm ASSIGNS_ABSORB_SAME_COMPONENTS in
  MP th (WEAKLY_VALID_COMPONENT_CONV(lhand(concl th)));;

(*** Examples

ASSIGNS_IDEMPOT_RULE `memory :> bytes16 a :> bitelement 1`;;

ASSIGNS_IDEMPOT_RULE `ZF`;;

ASSIGNS_IDEMPOT_RULE `Q22`;;

ASSIGNS_IDEMPOT_RULE `Q22 :> asnumber`;;

 ***)

(* ------------------------------------------------------------------------- *)
(* Commute `ASSIGNS c ,, ASSIGNS d` (don't absorb even if possible).         *)
(* This will work pretty generally, but "zerotop_32" spoils things. It's OK. *)
(* We'll never purposely put both in a modifies list and the automatic ones  *)
(* will all expand to something happening on the full space anyway.          *)
(* ------------------------------------------------------------------------- *)

let ASSIGNS_SWAP_TAC =
  let pth = REFL `ASSIGNS c ,, ASSIGNS d` in
  let toptac = CONV_TAC(BINOP_CONV(BINOP_CONV ASSIGNS_CANON_CONV)) in
  let basetac =
    MATCH_ACCEPT_TAC pth ORELSE
    MATCH_ACCEPT_TAC ASSIGNS_SWAP_ELEMENTS ORELSE
    MATCH_ACCEPT_TAC ASSIGNS_SWAP_BITELEMENTS ORELSE
    MATCH_ACCEPT_TAC ASSIGNS_SWAP_BYTES ORELSE
    MATCH_ACCEPT_TAC ASSIGNS_SWAP_ELEMENT_BYTES ORELSE
    MATCH_ACCEPT_TAC(GSYM ASSIGNS_SWAP_ELEMENT_BYTES) ORELSE
    (MATCH_MP_TAC ASSIGNS_SWAP_SUBCOMPONENTS_L THEN CONJ_TAC THENL
      [CONV_TAC VALID_COMPONENT_CONV;
       CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV]) ORELSE
    (MATCH_MP_TAC ASSIGNS_SWAP_SUBCOMPONENTS_R THEN CONJ_TAC THENL
      [CONV_TAC VALID_COMPONENT_CONV;
       CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV]) in
  let rec maintac g =
    (basetac ORELSE
     (MATCH_MP_TAC ASSIGNS_SWAP_SUBCOMPONENTS THEN CONJ_TAC THENL
       [CONV_TAC VALID_COMPONENT_CONV;
        toptac THEN maintac])) g in
  (toptac THEN maintac) ORELSE
  (* ORTHOGONAL_COMPONENTS_CONV can be expensive; rely on it as the last
     resort. *)
  (MATCH_MP_TAC ASSIGNS_SWAP_ORTHOGONAL_COMPONENTS THEN
     CONV_TAC ORTHOGONAL_COMPONENTS_CONV);;

(* A cache that stores `ASSIGNS x ,, ASSIGNS y` theorems.
   `assoc y !(assoc x !assigns_swap_conv_cache)` must return the
   theorem, if the entry exists. *)
let assigns_swap_conv_cache:
    (term * ((term * thm) list ref)) list ref = ref [];;

let ASSIGNS_SWAP_CONV tm =
  match tm with
    Comb(Comb((Const(",,",_) as stm),
              (Comb(Const("ASSIGNS",_),x) as ctm)),
         (Comb(Const("ASSIGNS",_),y) as dtm)) ->
      if ctm = dtm then REFL tm else
      let the_goal:term = mk_eq(tm,mk_comb(mk_comb(stm,dtm),ctm)) in
      if is_const(x) && is_const(y) then
        (* Use cache if x and y are constants, e.g., `PC` and `X1`. *)
        try
          let lref = assoc x !assigns_swap_conv_cache in
          try assoc y !lref
          with Failure _ ->
            let newth = prove(the_goal,ASSIGNS_SWAP_TAC) in
            lref := (y, newth)::!lref; newth
        with Failure _ ->
          let newth = prove(the_goal,ASSIGNS_SWAP_TAC) in
          assigns_swap_conv_cache := (x, ref [(y,newth)])::!assigns_swap_conv_cache;
          newth
      else
        prove(the_goal,ASSIGNS_SWAP_TAC)
  | _ -> failwith "ASSIGNS_SWAP_CONV";;

(*** Examples:

ASSIGNS_SWAP_CONV `ASSIGNS memory ,, ASSIGNS X11`;;

ASSIGNS_SWAP_CONV `ASSIGNS (memory :> bytes(a,b)) ,, ASSIGNS X11`;;

ASSIGNS_SWAP_CONV
  `ASSIGNS (memory :> bytes(a,b)) ,, ASSIGNS (memory :> bytes16 c)`;;

ASSIGNS_SWAP_CONV `ASSIGNS W11 ,, ASSIGNS X12`;;

ASSIGNS_SWAP_CONV
  `ASSIGNS (X1 :> bitelement 1) ,, ASSIGNS (X1 :> bitelement 2)`;;

*** This one is false because of the zeroing of the top half

ASSIGNS_SWAP_CONV `ASSIGNS W1 ,, ASSIGNS X1`;;

*** This one is true and should really work but it's not really useful

ASSIGNS_SWAP_CONV
  `ASSIGNS (memory :> bytes16 a :> bitelement 1) ,,
   ASSIGNS (memory :> bytes8 b :> bitelement 3)`;;

***)

(* ------------------------------------------------------------------------- *)
(* Canonize ASSIGNS / MAYCHANGE chain into right-assoc ASSIGNS only.         *)
(* In the degenerate case it will be just (=).                               *)
(* ------------------------------------------------------------------------- *)

let MAYCHANGE_CANON_CONV =
  GEN_REWRITE_CONV TOP_DEPTH_CONV
   [MAYCHANGE; SEQ_ID; GSYM SEQ_ASSOC];;

(*** Example

MAYCHANGE_CANON_CONV
 `ASSIGNS X1 ,, MAYCHANGE [X3; X4] ,, MAYCHANGE [] ,, ASSIGNS X11`;;

 ***)

(* ------------------------------------------------------------------------- *)
(* Prove equality relation is subsumed by a MAYCHANGE/ASSIGNS sequence       *)
(* ------------------------------------------------------------------------- *)

let SUBSUMED_ID_MAYCHANGE_TAC =
  CONV_TAC(RAND_CONV MAYCHANGE_CANON_CONV) THEN
  REPEAT(MATCH_MP_TAC SUBSUMED_ID_SEQ THEN CONJ_TAC) THEN
  TRY(MATCH_ACCEPT_TAC(ISPEC `(=)` SUBSUMED_REFL)) THEN
  MATCH_MP_TAC SUBSUMED_ID_EXTENSIONALLY_VALID_COMPONENT THEN
  CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV THEN NO_TAC;;

(*** Example (ARM)

g `(=) subsumed
  (ASSIGNS (memory :> bytes(a,b)) ,, (=) ,, MAYCHANGE [CF; NF])`;;

e SUBSUMED_ID_MAYCHANGE_TAC;;

****)

(* ------------------------------------------------------------------------- *)
(* Given (a_1 ,, ... ,, a_n) ,, b, commute b leftwards down the chain until  *)
(* either you eliminate it using the argument conversion (typically when you *)
(* absorb it into the same component) or you get right back to the start, or *)
(* you get stuck. The returned value is +1 for absorption, 0 for commuting   *)
(* to the start and -1 for getting stuck in the middle.                      *)
(* ------------------------------------------------------------------------- *)

let rec ASSIGNS_MOVE_BACK_CONV acv tm =
  try let th0 = GEN_REWRITE_CONV I [GSYM SEQ_ASSOC] tm in
      let ltm,rtm = dest_comb(rand(concl th0)) in
      let (p,th1) = ASSIGNS_MOVE_BACK_CONV acv rtm in
      let th2 = TRANS th0 (AP_TERM ltm th1) in
      if p <> 0 then (p,th2) else
      let th3 = GEN_REWRITE_RULE RAND_CONV [SEQ_ASSOC] th2 in
      (try 1,CONV_RULE (RAND_CONV (LAND_CONV acv)) th3
       with Failure _ -> try
         let th4 = CONV_RULE (RAND_CONV (LAND_CONV ASSIGNS_SWAP_CONV)) th3 in
         0,GEN_REWRITE_RULE RAND_CONV [GSYM SEQ_ASSOC] th4
       with Failure _ -> -1,th2)
  with Failure _ -> try 1,acv tm
  with Failure _ -> try 0,ASSIGNS_SWAP_CONV tm
  with Failure _ -> -1,REFL tm;;

(**** Examples

ASSIGNS_MOVE_BACK_CONV NO_CONV
 `(ASSIGNS X1 ,, ASSIGNS X2 ,, ASSIGNS X3 ,, ASSIGNS X4) ,,
   ASSIGNS X11`;;

ASSIGNS_MOVE_BACK_CONV ASSIGNS_IDEMPOT_CONV
 `(ASSIGNS X1 ,, ASSIGNS X2 ,, ASSIGNS X3 ,, ASSIGNS X4) ,,
   ASSIGNS X11`;;

ASSIGNS_MOVE_BACK_CONV ASSIGNS_IDEMPOT_CONV
 `(ASSIGNS X1 ,, ASSIGNS X2 ,, ASSIGNS X3 ,, ASSIGNS X4) ,,
   ASSIGNS X3`;;

ASSIGNS_MOVE_BACK_CONV ASSIGNS_IDEMPOT_CONV
 `(ASSIGNS X1 ,, ASSIGNS X2 ,, ASSIGNS X3 ,, ASSIGNS X4) ,,
   ASSIGNS W2`;;

 ***)

(* ------------------------------------------------------------------------- *)
(* Now implement idempotence for a whole chain of ASSIGNS clauses.           *)
(* ASSIGNS_SEQ_ABSORB_CONV takes a term of the form                         *)
(* (ASSIGNS a1 ,, ... ,, ASSIGNS an) ,, (ASSIGNS b1 ,, ... ASSIGNS bm)       *)
(* where each bi occurs somewhere in the a list that it can be commuted      *)
(* back to and absorbed by in sequence. In the common case the a and b lists *)
(* are identical. Returns equality with just the a's list.                   *)
(* ------------------------------------------------------------------------- *)

let rec ASSIGNS_SEQ_ABSORB_CONV tm =
  match tm with
    Comb(Comb(Const(",,",_),_),Comb(Comb(Const(",,",_),_),_)) ->
      let th0 = GEN_REWRITE_CONV I [SEQ_ASSOC] tm in
      let lop,rtm = dest_comb(rand(concl th0)) in
      let op,ltm = dest_comb lop in
      let n,th1 = ASSIGNS_MOVE_BACK_CONV ASSIGNS_IDEMPOT_CONV ltm in
      if n <> 1 then failwith "ASSIGNS_SEQ_ABSORB_CONV" else
      let th2 = TRANS th0 (AP_THM (AP_TERM op th1) rtm) in
      TRANS th2 (ASSIGNS_SEQ_ABSORB_CONV (rand(concl th2)))
  | _ ->
      let n,th = ASSIGNS_MOVE_BACK_CONV ASSIGNS_IDEMPOT_CONV tm in
      if n <> 1 then failwith "ASSIGNS_SEQ_ABSORB_CONV" else th;;

let ASSIGNS_SEQ_IDEMPOT_CONV tm =
  match tm with
    Comb(Comb(Const(",,",_),ltm),rtm) when ltm = rtm ->
        ASSIGNS_SEQ_ABSORB_CONV tm
  | _ -> failwith "ASSIGNS_SEQ_IDEMPOT_CONV: Non-identical sequences";;

(* ------------------------------------------------------------------------- *)
(* Tactic to prove FRAMES ,, FRAMES = FRAMES where FRAMES is a ,,-sequence   *)
(* of ASSIGNS and CHANGES statements.                                        *)
(* ------------------------------------------------------------------------- *)

let MAYCHANGE_IDEMPOT_TAC =
  let the_truth = `true` in
  fun (asl,w as gl) ->
    match w with
      Comb(Comb(Const("=",_) as etm,Comb(Comb(Const(",,",_) as ctm,ltm),rtm)),stm)
          when ltm = stm && rtm = stm ->
        if is_gabs ltm && snd (strip_gabs ltm) = the_truth then
          MATCH_ACCEPT_TAC SEQ_TRIVIAL gl
        else
          let th1 = MAYCHANGE_CANON_CONV stm in
          let th2 = MK_BINOP ctm (th1,th1) in
          let th3 = MK_BINOP etm (th2,th1) in
          let th4 = if is_const(rand(concl th1))
                    then ISPEC (rand(concl th1)) (CONJUNCT1 SEQ_ID)
                    else ASSIGNS_SEQ_IDEMPOT_CONV(lhand(rand(concl th3))) in
          ACCEPT_TAC (EQ_MP (SYM th3) th4) gl
    | _ -> failwith "MAYCHANGE_IDEMPOT_TAC";;

(*** Examples

  g `MAYCHANGE [X1; X2] ,, MAYCHANGE [X1; X2] = MAYCHANGE [X1; X2]`;;
  e MAYCHANGE_IDEMPOT_TAC;;

  g `MAYCHANGE [memory] ,, MAYCHANGE [memory] = MAYCHANGE [memory]`;;
  e MAYCHANGE_IDEMPOT_TAC;;

  g
  `(MAYCHANGE [X1; X11; X13] ,, MAYCHANGE [ZF] ,, ASSIGNS (memory :> bytes8 a))
   ,,
   (MAYCHANGE [X1; X11; X13] ,, MAYCHANGE [ZF] ,, ASSIGNS (memory :> bytes8 a))
   =
   (MAYCHANGE [X1; X11; X13] ,, MAYCHANGE [ZF] ,, ASSIGNS (memory :> bytes8 a))
   `;;
  e MAYCHANGE_IDEMPOT_TAC;;

  g `MAYCHANGE([]:((A,B)component)list) ,,
     MAYCHANGE([]:((A,B)component)list) =
     MAYCHANGE([]:((A,B)component)list)`;;
  e MAYCHANGE_IDEMPOT_TAC;;

****)

(* ------------------------------------------------------------------------- *)
(* Identify a "MAYCHANGE"-containing term.                                   *)
(* ------------------------------------------------------------------------- *)

let maychange_term =
  let pred t = match t with
    Const("MAYCHANGE",_) -> true
  | _ -> false in
  can (find_term pred);;

(* ------------------------------------------------------------------------- *)
(* Produce a modified update list given theorems                             *)
(* th = |- (MAYCHANGE [....] ,, MAYCHANGE [...] ... ) s0 s1                  *)
(* uth = |- write c1 y1 (write c2 y2 (write .... s1)) = s2                   *)
(* give back                                                                 *)
(* th' = |- (MAYCHANGE [....] ,, MAYCHANGE [...] ... ) s0 s1                 *)
(* Tries to absorb components already in the list, otherwise                 *)
(* simply appends them individually. Not optimal but OK.                     *)
(* ------------------------------------------------------------------------- *)

let MAYCHANGE_UPDATE_RULE =
  let JUSTADD_CONV =
    GEN_REWRITE_CONV I [MAYCHANGE_LID] ORELSEC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [GSYM SEQ_ASSOC] in
  let MAYCHANGE_SIMPLE_ABSORB_CONV tm =
    match tm with
      Comb(Comb(Const(",,",_) as cop,ltm),rtm) ->
          let lth = MAYCHANGE_CANON_CONV ltm
          and rth = MAYCHANGE_CANON_CONV rtm in
          let tm' = mk_comb(mk_comb(cop,rand(concl lth)),rand(concl rth)) in
          let n,eth = ASSIGNS_MOVE_BACK_CONV ASSIGNS_IDEMPOT_CONV tm' in
          if n <> 1 then JUSTADD_CONV tm else
          let th' = MK_COMB(AP_TERM cop lth,rth) in
          TRANS (TRANS th' eth) (SYM lth)
    | _ -> failwith "MAYCHANGE_SIMPLE_ABSORB_CONV" in
  let rec BASIC_MAYCHANGE_UPDATE_RULE tm th =
      match tm with
        Comb(Comb(Comb(Const("write",_),c),y),s) ->
           let th1 = BASIC_MAYCHANGE_UPDATE_RULE s th in
           let th2 = ISPECL [c;y] (MATCH_MP MAYCHANGE_WRITE th1) in
           CONV_RULE(RATOR_CONV(RATOR_CONV MAYCHANGE_SIMPLE_ABSORB_CONV)) th2
      | _ -> th in
  fun uth th ->
    let th' = BASIC_MAYCHANGE_UPDATE_RULE (lhand(concl uth)) th in
    EQ_MP (AP_TERM (rator(concl th')) uth) th';;

(*** Example

let th = ASSUME `(MAYCHANGE [PC; X19] ,, MAYCHANGE [CF]) s s'`
and uth = ASSUME
 `write VF
      (~(ival (read X0 s1) - ival (read X1 s1) =
         ival (word_sub (read X0 s1) (read X1 s1))))
     (write CF (~(val (read X0 s1) < val (read X1 s1)))
     (write ZF (val (word_sub (read X0 s1) (read X1 s1)) = 0)
     (write NF (ival (word_sub (read X0 s1) (read X1 s1)) < &0)
     (write X1 (word_sub (read X0 s1) (read X1 s1))
     (write PC (word (pc + 8)) s'))))) = s''`;;

MAYCHANGE_UPDATE_RULE uth th;;

 ***)

(* ------------------------------------------------------------------------- *)
(* Produce updated "MAYCHANGE" assumption from one in assumptions.           *)
(* Absorbs simple duplicates but otherwise doesn't try to be clever.         *)
(* Works from antecedent in the goal specifying the state update.            *)
(* ------------------------------------------------------------------------- *)

let MAYCHANGE_STATE_UPDATE_TAC =
  DISCH_THEN(fun uth ->
    MP_TAC uth THEN
    FIRST_X_ASSUM(ASSUME_TAC o MAYCHANGE_UPDATE_RULE uth o
           check(maychange_term o concl)));;

(* ------------------------------------------------------------------------- *)
(* A property P always becomes true "eventually". This correctly reflects    *)
(* nondeterminism: we need the property to hold eventually along *every*     *)
(* possible path from the initial state. It also requires (unless P already  *)
(* holds in the initial state) that there *is* indeed a successor state, so  *)
(* the "on all paths from the current state" quantifier never holds          *)
(* degenerately because there are no such paths.                             *)
(* ------------------------------------------------------------------------- *)

let eventually_RULES,eventually_INDUCT,eventually_CASES =
  new_inductive_definition
   `(forall s.
        P s ==> (eventually:(A->A->bool)->(A->bool)->A->bool) step P s) /\
    (forall s.
        (exists s'. step s s') /\
        (forall s'. step s s' ==> eventually step P s')
          ==> eventually step P s)`;;

let EVENTUALLY_MONO = prove
 (`forall (step:A->A->bool) P Q.
          (forall s. P s ==> Q s)
          ==> (forall s. eventually step P s ==> eventually step Q s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC eventually_INDUCT THEN
  ASM_MESON_TAC[eventually_RULES]);;

let EVENTUALLY_IMP_EVENTUALLY = prove
 (`forall (step:A->A->bool) P Q.
          (forall s. eventually step P s ==> eventually step Q s) <=>
          (forall s. P s ==> eventually step Q s)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[eventually_RULES]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC eventually_INDUCT THEN
  ASM_REWRITE_TAC[eventually_RULES]);;

let EVENTUALLY_EVENTUALLY = prove
 (`forall (step:A->A->bool) P.
          eventually step (eventually step P) = eventually step P`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_AND_THM; TAUT
   `(p <=> q) <=> (p ==> q) /\ (q ==> p)`] THEN
  REWRITE_TAC[eventually_RULES] THEN
  REWRITE_TAC[EVENTUALLY_IMP_EVENTUALLY; eventually_RULES]);;


let EVENTUALLY_P_INOUT = prove(
  `forall (s0:S). P /\ eventually step (\s. Q s) s0 <=>
            eventually step (\s. P /\ Q s) s0`,
  ASM_CASES_TAC `P:bool` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[TAUT`~p <=> (p ==> F)`] THEN
  MATCH_MP_TAC eventually_INDUCT THEN MESON_TAC[]);;

let EVENTUALLY_DISJ1 = prove(
  `forall (step:S->S->bool) P Q s.
    eventually step (\s. P s) s ==> eventually step (\s. P s \/ Q s) s`,
  REPEAT_N 3 GEN_TAC THEN MATCH_MP_TAC EVENTUALLY_MONO THEN MESON_TAC[]);;

let EVENTUALLY_DISJ2 = prove(
  `forall (step:S->S->bool) P Q s.
    eventually step (\s. Q s) s ==> eventually step (\s. P s \/ Q s) s`,
  REPEAT_N 3 GEN_TAC THEN MATCH_MP_TAC EVENTUALLY_MONO THEN MESON_TAC[]);;

let EVENTUALLY_TRIVIAL = prove(
  `forall (step:S->S->bool) s. eventually step (\s.T) s`,
  MESON_TAC[eventually_CASES]);;

let EVENTUALLY_CONSTANT = prove(
  `forall (s0:S). eventually step (\s. P) s0 <=> P`,
  ONCE_REWRITE_TAC[TAUT `(\(s:S). P) = \(s:S). (P /\ (\(s2:S). T) s)`] THEN
  REWRITE_TAC[GSYM EVENTUALLY_P_INOUT] THEN
  STRIP_TAC THEN ASM_CASES_TAC `P:bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (CONJUNCT1 (ISPECL [`step:S->S->bool`;`\(s:S). T`] eventually_RULES)) THEN MESON_TAC[]);;

let EVENTUALLY_EXISTS = prove(
  `forall (step:S->S->bool) (P:S->T->bool) (s:S).
    (exists x. eventually step (\s'. P s' x) s) ==>
    eventually step (\s'. exists x. P s' x) s`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `eventually (step:S->S->bool) (\s'. P s' (x:T)) s` THEN
  SPEC_TAC (`s:S`,`s:S`) THEN
  MATCH_MP_TAC EVENTUALLY_MONO THEN MESON_TAC[]);;

let EVENTUALLY_IMP_INOUT = prove(
  `forall (step:S->S->bool) P (Q:S->bool) s.
    (P ==> eventually step (\s'. Q s') s) <=>
    (P ==> eventually step (\s'. P /\ Q s') s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `eventually (step:S->S->bool) (\s'. Q s') s` MP_TAC THENL
    [ASM_MESON_TAC[];ALL_TAC] THEN
    SPEC_TAC (`s:S`,`s:S`) THEN MATCH_MP_TAC EVENTUALLY_MONO THEN BETA_TAC THEN ASM_REWRITE_TAC[];

    ASM_CASES_TAC `P:bool` THEN ASM_REWRITE_TAC[]
  ]);;

(* ------------------------------------------------------------------------- *)
(* A more explicit and non-inductive equivalent of "eventually R P s":       *)
(* starting in state s there is no infinite sequence of non-P states         *)
(* nor a finite sequence of non-P states ending in a stuck state, where      *)
(* all sequences have adjacent pairs connected by the relation.              *)
(* ------------------------------------------------------------------------- *)

let EVENTUALLY_SEQUENTIALLY = prove
 (`!R p s:A.
        eventually R p s <=>
        ~(?x:num->A. x 0 = s /\
                     (!n. R (x n) (x(n + 1))) /\
                     (!n. ~p(x n))) /\
        ~(?N x:num->A. x 0 = s /\
                       (!n. n < N ==> R (x n) (x(n + 1))) /\
                       (!n. ~p(x n)) /\
                       ~(?s'. R (x N) s'))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TAUT
   `(p <=> q /\ r) <=> (p ==> q) /\ (p ==> r) /\ (~p ==> ~q \/ ~r)`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[NOT_EXISTS_THM] THEN SPEC_TAC(`s:A`,`s:A`) THEN
    MATCH_MP_TAC eventually_INDUCT THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `s:A` THEN DISCH_TAC THEN
    X_GEN_TAC `x:num->A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(x:num->A) 1` o CONJUNCT2) THEN
    REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[ADD_CLAUSES]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `\i. (x:num->A) (i + 1)`) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `!n:num. n <= N ==> eventually R (p:A->bool) (x n)`
    (MP_TAC o SPEC `N:num`) THENL
     [ALL_TAC; ASM_MESON_TAC[eventually_CASES; LE_REFL]] THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[LE_SUC_LT; ADD1] THEN
    ASM_MESON_TAC[eventually_CASES; LT_IMP_LE];
    DISCH_TAC THEN GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
    REWRITE_TAC[OR_EXISTS_THM] THEN
    SUBGOAL_THEN
      `?x. x 0 = (s:A) /\ (!n. ~eventually R p (x n)) /\
           (!n s'. R (x n) s' ==> R (x n) (x(SUC n)))`
    MP_TAC THENL
     [MATCH_MP_TAC DEPENDENT_CHOICE_FIXED THEN
      ASM_MESON_TAC[eventually_CASES];
      MATCH_MP_TAC MONO_EXISTS] THEN
    X_GEN_TAC `x:num->A` THEN ONCE_REWRITE_TAC[eventually_CASES] THEN
    REWRITE_TAC[ADD1; DE_MORGAN_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `!n:num. ?s'. (R:A->A->bool) (x n) s'` THENL
     [ASM_MESON_TAC[]; DISJ2_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Traditional Hoare triples, with a few rules.                              *)
(* ------------------------------------------------------------------------- *)

let hoare = define
 `hoare (step:A->A->bool) pre post <=> !s. pre s ==> eventually step post s`;;

let HOARE_PRECONDITION = prove
 (`forall (step:A->A->bool) pre pre' post.
      hoare step pre post /\ (!s. pre' s ==> pre s) ==> hoare step pre' post`,
  REWRITE_TAC[hoare] THEN MESON_TAC[]);;

let HOARE_POSTCONDITION = prove
 (`forall (step:A->A->bool) pre post post'.
        hoare step pre post /\ (!s. post s ==> post' s)
        ==> hoare step pre post'`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[hoare] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP EVENTUALLY_MONO) THEN SIMP_TAC[ETA_AX]);;

let HOARE = prove
 (`forall step pre post:A->bool.
        hoare step pre post <=>
        !s. eventually step pre s ==> eventually step post s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hoare] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o ISPEC `step:A->A->bool` o
      MATCH_MP EVENTUALLY_MONO) THEN
    REWRITE_TAC[EVENTUALLY_EVENTUALLY; ETA_AX];
    MESON_TAC[eventually_RULES]]);;

let HOARE_TRANS = prove
 (`forall (step:A->A->bool) pre mid post.
      hoare step pre mid /\ hoare step mid post ==> hoare step pre post`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [HOARE] THEN
  REWRITE_TAC[hoare] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A variant with an explicit frame condition or action in the TLA sense.    *)
(* ------------------------------------------------------------------------- *)

let ensures = define
 `ensures (step:A->A->bool) precondition postcondition frame <=>
        forall s. precondition s
            ==> eventually step (\s'. postcondition s' /\ frame s s') s`;;

let ENSURES_TRIVIAL = prove
 (`forall (step:A->A->bool) q f. ensures step (\x. F) q f`,
  REWRITE_TAC[ensures]);;

let ENSURES_ALREADY = prove
 (`forall (step:A->A->bool) p q r.
        (!x. p x ==> q x) /\ (=) subsumed r ==> ensures step p q r`,
  REWRITE_TAC[ensures; subsumed] THEN MESON_TAC[eventually_CASES]);;


(* ------------------------------------------------------------------------- *)
(*     Hoare Logic with the number of small steps explicitly annotated.      *)
(* Tactics in this file (common/relationa.ml) will support both 'ensures'    *)
(* and ensures_n.                                                            *)
(* ------------------------------------------------------------------------- *)

needs "common/relational_n.ml";;

(* If t is 'ensures ...' or 'eventually ...', return x
   If t is 'ensures_n ...' or 'eventually_n ...', return y
   Otherwise, raise a failure *)
let ensures_or_ensures_n (w:term) (x:'a) (y:'a): 'a =
  let c,_ = strip_comb w in
  let n = name_of c in
  if n = "ensures" || n = "eventually" then x
  else if n = "ensures_n" || n = "eventually_n" then y
  else failwith
          ("The term is neither ensures, eventually, ensures_n or " ^
                     "eventually_n");;

let ENSURES_OR_ENSURES_N_TAC tac_for_ensures tac_for_ensures_n: tactic =
  W(fun (asl,w) ->
      ensures_or_ensures_n w tac_for_ensures tac_for_ensures_n);;


(* ------------------------------------------------------------------------- *)
(* Initialization of breaking down an "ensures" triple                       *)
(* ------------------------------------------------------------------------- *)

let ENSURES_INIT_TAC sname =
  ENSURES_OR_ENSURES_N_TAC
      (GEN_REWRITE_TAC I [ensures])
      (GEN_REWRITE_TAC I [ensures_n])
      THEN
  BETA_TAC THEN
  W(fun (asl,w) ->
        let ty = type_of(fst(dest_forall w)) in
        let svar = mk_var(sname,ty) in
        X_GEN_TAC svar THEN
        DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
        ASSUME_TAC(ISPEC svar MAYCHANGE_STARTER));;

(* ------------------------------------------------------------------------- *)
(* Additional pre-simulation canonizations.                                  *)
(* ------------------------------------------------------------------------- *)

let simulation_precanon_thms = ref ([]:thm list);;

(* ------------------------------------------------------------------------- *)
(* Classic precondition strengthening and postcondition weakening.           *)
(* Implement also (essentially trivial) tactics to apply it.                 *)
(* ------------------------------------------------------------------------- *)

let ENSURES_PRECONDITION_THM_GEN = prove
 (`forall (P:A->bool) P' C C' Q.
        (!x. P' x ==> P x) /\
        (!x y. C x y ==> C' x y) /\
        ensures step P Q C
        ==> ensures step P' Q C'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ensures] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_MONO) THEN
  ASM_SIMP_TAC[]);;

let ENSURES_PRECONDITION_THM = prove
 (`forall (P:A->bool) P' C Q.
        (!x. P' x ==> P x) /\
        ensures step P Q C
        ==> ensures step P' Q C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ensures] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_MONO) THEN
  ASM_SIMP_TAC[]);;

let ENSURES_PRECONDITION_TAC p' =
  ENSURES_OR_ENSURES_N_TAC
      (MATCH_MP_TAC ENSURES_PRECONDITION_THM)
      (MATCH_MP_TAC ENSURES_N_PRECONDITION_THM) THEN
  EXISTS_TAC p';;

let ENSURES_POSTCONDITION_THM_GEN = prove
 (`forall (P:A->bool) C C' Q Q'.
    (forall x. Q x ==> Q' x) /\
    (forall x y. C x y ==> C' x y) /\
    ensures step P Q C
    ==> ensures step P Q' C'`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ensures] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_MONO) THEN
  ASM_SIMP_TAC[]);;

let ENSURES_POSTCONDITION_THM = prove
 (`forall (P:A->bool) C Q Q'.
        (forall x. Q x ==> Q' x) /\
        ensures step P Q C
        ==> ensures step P Q' C`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ensures] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_MONO) THEN
  ASM_SIMP_TAC[]);;

let ENSURES_POSTCONDITION_TAC q' =
  ENSURES_OR_ENSURES_N_TAC
      (MATCH_MP_TAC ENSURES_POSTCONDITION_THM)
      (MATCH_MP_TAC ENSURES_N_POSTCONDITION_THM) THEN
  EXISTS_TAC q';;

let ENSURES_PREPOSTCONDITION_THM = prove
 (`forall (P:A->bool) P' C Q Q'.
        (forall x. P' x ==> P x) /\ (!x. Q x ==> Q' x) /\
        ensures step P Q C
        ==> ensures step P' Q' C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ensures] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_MONO) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The analogous monotonicity result for the frame.                          *)
(* ------------------------------------------------------------------------- *)

let ENSURES_FRAME_MONO = prove
 (`forall (P:A->bool) Q C C'.
        (!x y. C x y ==> C' x y) /\
        ensures step P Q C
        ==> ensures step P Q C'`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ensures] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_MONO) THEN
  ASM_SIMP_TAC[]);;

let ENSURES_FRAME_SUBSUMED = prove
 (`forall (P:A->bool) Q C C'.
        C subsumed C' /\
        ensures step P Q C
        ==> ensures step P Q C'`,
  REWRITE_TAC[subsumed; ENSURES_FRAME_MONO]);;

(* ------------------------------------------------------------------------- *)
(* Carry a frame-stable predicate through an existing ensures theorem.       *)
(*                                                                           *)
(* ENSURES_FRAME_INVARIANT strengthens both the precondition and the         *)
(* postcondition with J, provided J is preserved by the existing frame C.    *)
(* It keeps C unchanged and reuses the original theorem without replaying    *)
(* the transition proof.                                                     *)
(*                                                                           *)
(* This is a specialization of ENSURES_SUBLEMMA_THM with identical source    *)
(* and target frames. The generic rule can derive the same result, but each  *)
(* caller must spell out the projection P /\ J ==> P, reflexive frame        *)
(* subsumption, and reconstruction of Q /\ J. ENSURES_FRAME_SUBSUMED instead *)
(* widens the permitted frame. ENSURES_PRESERVED_TAC and                     *)
(* ENSURES_EXISTING_PRESERVED_TAC remove a particular component from a       *)
(* temporary MAYCHANGE frame after proving its value is restored; they do    *)
(* not add an arbitrary invariant to an already-proved theorem.              *)
(*                                                                           *)
(* This specialization supports modular machine proofs with narrow inner     *)
(* contracts. An inner NTT phase can omit a read-only table after loading    *)
(* its entries into registers, while an enclosing loop still needs the       *)
(* table predicate for later phases. Carrying it with this rule keeps the    *)
(* phase theorem reusable and avoids replaying symbolic execution or         *)
(* expanding generic sublemma boilerplate at every use.                      *)
(* ------------------------------------------------------------------------- *)

let ENSURES_FRAME_INVARIANT = prove
 (`!step P Q C (J:A->bool).
      (!s s'. J s /\ C s s' ==> J s') /\
      ensures step P Q C
      ==> ensures step
           (\s. P s /\ J s)
           (\s. Q s /\ J s)
           C`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ensures] THEN
  STRIP_TAC THEN
  X_GEN_TAC `s:A` THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:A`) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC
   (REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_MONO) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Classic Hoare sequencing / Transitivity rule.                             *)
(* ------------------------------------------------------------------------- *)

let ENSURES_TRANS = prove
 (`forall step P Q R C1 C2:A->A->bool.
        ensures step P Q C1 /\ ensures step Q R C2
        ==> ensures step P R (C1 ,, C2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures] THEN DISCH_TAC THEN
  X_GEN_TAC `s:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 (MP_TAC o SPEC `s:A`) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!s'. Q s' /\ (C1:A->A->bool) s s'
         ==> eventually step (\s'. R s' /\ (C1 ,, C2) s s') s'`
  MP_TAC THENL
   [X_GEN_TAC `s':A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s':A`) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM]
        EVENTUALLY_MONO) THEN
    REWRITE_TAC[seq] THEN ASM_MESON_TAC[];
    GEN_REWRITE_TAC LAND_CONV [GSYM EVENTUALLY_IMP_EVENTUALLY] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let ENSURES_TRANS_SIMPLE = prove
 (`forall (P:A->bool) Q R C.
        C ,, C = C /\
        ensures step P Q C /\ ensures step Q R C
        ==> ensures step P R C`,
  MESON_TAC[ENSURES_TRANS]);;

let ENSURES_SEQUENCE_TAC =
  let pth = prove
   (`forall program_decodes pcounter pc' Q.
        C ,, C = C /\
        ensures step (\s. program_decodes s /\
                          read pcounter s = word pc'' /\
                          P s)
                     (\s. program_decodes s /\
                          read pcounter s = word pc' /\
                          Q s)
                     C /\
        ensures step (\s. program_decodes s /\
                          read pcounter s = word pc' /\
                          Q s)
                     R C
        ==> ensures step (\s. program_decodes s /\
                              read pcounter s = word pc'' /\
                              P s)
                          R C`,
    REWRITE_TAC[ENSURES_TRANS_SIMPLE]) in
  let tac = MATCH_MP_TAC pth in
  fun n q -> (tac THEN MAP_EVERY EXISTS_TAC [n;q] THEN BETA_TAC THEN
              CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]);;

let ENSURES_N_SEQUENCE_TAC =
  let pth = prove
   (`!(program_decodes:A->bool) (pcounter:(A,B word)component) pc' Q n1 n2 n3.
        C ,, C = C /\
        ensures_n step (\s. program_decodes s /\
                          read pcounter s = word pc'' /\
                          P s)
                       (\s. program_decodes s /\
                          read pcounter s = word pc' /\
                          Q s)
                       C (\s. n1) /\
        ensures_n step (\s. program_decodes s /\
                          read pcounter s = word pc' /\
                          Q s)
                       R C (\s. n2) /\
        n3 = n1 + n2
        ==> ensures_n step (\s. program_decodes s /\
                              read pcounter s = word pc'' /\
                              P s)
                           R C (\s. n3)`,
    MESON_TAC[ENSURES_N_TRANS_SIMPLE]) in
  let tac = MATCH_MP_TAC pth in
  fun pc q n1 n2 -> (tac THEN MAP_EVERY EXISTS_TAC [pc;q;n1;n2] THEN BETA_TAC THEN
              CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Case analysis at "ensures" level, often used at a branch instruction.     *)
(* ------------------------------------------------------------------------- *)

let ENSURES_CASES_TAC =
  let pth = prove
   (`!B. ensures step (\s. program_decodes s /\
                           read pcounter s = word pc' /\
                           B s /\ P s)
                      Q C /\
        ensures step (\s. program_decodes s /\
                          read pcounter s = word pc' /\
                           ~B s /\ P s)
                      Q C
        ==> ensures step (\s. program_decodes s /\
                              read pcounter s = word pc' /\
                              P s)
                         Q C`,
    REWRITE_TAC[ensures] THEN LEANCOP_TAC[]) in
  fun q -> (MATCH_MP_TAC pth THEN EXISTS_TAC q THEN BETA_TAC);;

(* ------------------------------------------------------------------------- *)
(* Induction, basically a variant of the usual WHILE rule with a             *)
(* test at the end. Versions for up from 0...k-1, down from k-1...0 and up   *)
(* from a...b-1.                                                             *)
(* ------------------------------------------------------------------------- *)

let ENSURES_WHILE_UP_TAC,ENSURES_WHILE_DOWN_TAC,
    ENSURES_WHILE_AUP_TAC,ENSURES_WHILE_ADOWN_TAC =
  let pth = prove
   (`!k pc1 pc2 (loopinvariant:num->A->bool).
       C ,, C = C /\
       ~(k = 0) /\
       ensures step (\s. program_decodes s /\
                         read pcounter s = word pc /\
                         precondition s)
                    (\s. program_decodes s /\
                         read pcounter s = word pc1 /\
                         loopinvariant 0 s)
                    C /\
       (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  loopinvariant i s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  loopinvariant (i + 1) s)
                             C) /\
       (!i. 0 < i /\ i < k /\ ~(i = k) /\ ~(i = 0) /\ ~(k = 0) /\ 0 < k
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  loopinvariant i s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  loopinvariant i s)
                             C) /\
       ensures step (\s. program_decodes s /\
                         read pcounter s = word pc2 /\
                         loopinvariant k s)
                     postcondition
                     C
       ==> ensures step
             (\s. program_decodes s /\
                  read pcounter s = word pc /\
                  precondition s)
             postcondition
             C`,
    REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [IMP_CONJ] THEN
    DISCH_THEN(LABEL_TAC "*" o MATCH_MP
      (ONCE_REWRITE_RULE[IMP_CONJ] ENSURES_TRANS_SIMPLE)) THEN
    REWRITE_TAC[CONJ_ASSOC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    USE_THEN "*" (fun th ->
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] th)) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    USE_THEN "*" (fun th ->
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] th)) THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `~(k = 0) ==> k = (k - 1) + 1`)) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `~(k = 0) ==> k - 1 < k`)) THEN
    SPEC_TAC(`k - 1`,`j:num`) THEN MATCH_MP_TAC num_INDUCTION THEN
    ASM_REWRITE_TAC[ADD1] THEN CONJ_TAC THENL
     [STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `0` o CONJUNCT1) THEN
      ASM_ARITH_TAC;
      X_GEN_TAC `i:num`] THEN
    ASM_CASES_TAC `i + 1 < k` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `i + 1 < k ==> i < k`)) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "*" (fun th ->
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] th)) THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN (MP_TAC o SPEC `i + 1`)) THEN
    MATCH_MP_TAC(TAUT
     `(p /\ r) /\ (q /\ s ==> t) ==> (p ==> q) ==> (r ==> s) ==> t`) THEN
    ASM_REWRITE_TAC[ENSURES_TRANS_SIMPLE] THEN ASM_ARITH_TAC) in
  let qth = prove
   (`!k pc1 pc2 (loopinvariant:num->A->bool).
       C ,, C = C /\
       ~(k = 0) /\
       ensures step (\s. program_decodes s /\
                         read pcounter s = word pc /\
                         precondition s)
                    (\s. program_decodes s /\
                         read pcounter s = word pc1 /\
                         loopinvariant k s)
                    C /\
       (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  loopinvariant (i + 1) s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  loopinvariant i s)
                             C) /\
       (!i. 0 < i /\ i < k /\ ~(i = k) /\ ~(i = 0) /\ ~(k = 0) /\ 0 < k
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  loopinvariant i s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  loopinvariant i s)
                             C) /\
       ensures step (\s. program_decodes s /\
                         read pcounter s = word pc2 /\
                         loopinvariant 0 s)
                     postcondition
                     C
       ==> ensures step
             (\s. program_decodes s /\
                  read pcounter s = word pc /\
                  precondition s)
             postcondition
             C`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC[`k:num`; `pc1:num`; `pc2:num`;
                   `\i. (loopinvariant:num->A->bool) (k - i)`] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[SUB_0; SUB_REFL] THEN
    REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN REWRITE_TAC[]) THENL
     [DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k - (i + 1)`) THEN
      ASM_SIMP_TAC[ARITH_RULE `i < k ==> k - (i + 1) + 1 = k - i`] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]) in
  let rth = prove
   (`!a b pc1 pc2 (loopinvariant:num->A->bool).
       C ,, C = C /\
       a < b /\
       ensures step (\s. program_decodes s /\
                         read pcounter s = word pc /\
                         precondition s)
                    (\s. program_decodes s /\
                         read pcounter s = word pc1 /\
                         loopinvariant a s)
                    C /\
       (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  loopinvariant i s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  loopinvariant (i + 1) s)
                             C) /\
       (!i. a < i /\ i < b /\ ~(i = b) /\ ~(i = 0) /\
            ~(i = a) /\ ~(b = 0) /\ 0 < b
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  loopinvariant i s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  loopinvariant i s)
                             C) /\
       ensures step (\s. program_decodes s /\
                         read pcounter s = word pc2 /\
                         loopinvariant b s)
                     postcondition
                     C
       ==> ensures step
             (\s. program_decodes s /\
                  read pcounter s = word pc /\
                  precondition s)
             postcondition
             C`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`b - a:num`; `pc1:num`; `pc2:num`;
                          `\i. (loopinvariant:num->A->bool) (a + i)`] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[ARITH_RULE `a:num < b ==> a + b - a = b`] THEN
    REWRITE_TAC[ADD_ASSOC] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC) in
 let sth = prove
   (`!a b pc1 pc2 (loopinvariant:num->A->bool).
       C ,, C = C /\
       a < b /\
       ensures step (\s. program_decodes s /\
                         read pcounter s = word pc /\
                         precondition s)
                    (\s. program_decodes s /\
                         read pcounter s = word pc1 /\
                         loopinvariant b s)
                    C /\
       (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  loopinvariant (i + 1) s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  loopinvariant i s)
                             C) /\
       (!i. a < i /\ i < b /\ ~(i = a) /\ ~(i = 0) /\
            ~(i = b) /\ ~(b = 0) /\ 0 < b
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  loopinvariant i s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  loopinvariant i s)
                             C) /\
       ensures step (\s. program_decodes s /\
                         read pcounter s = word pc2 /\
                         loopinvariant a s)
                     postcondition
                     C
       ==> ensures step
             (\s. program_decodes s /\
                  read pcounter s = word pc /\
                  precondition s)
             postcondition
             C`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [`b - a:num`; `pc1:num`; `pc2:num`;
                          `\i. (loopinvariant:num->A->bool) (a + i)`] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[ARITH_RULE `a:num < b ==> a + b - a = b`] THEN
    REWRITE_TAC[ADD_ASSOC] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC) in
  (fun k pc1 pc2 iv ->
    (MATCH_MP_TAC pth THEN
     MAP_EVERY EXISTS_TAC [k; pc1; pc2; iv] THEN
     BETA_TAC THEN
     CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC])),
  (fun k pc1 pc2 iv ->
    (MATCH_MP_TAC qth THEN
     MAP_EVERY EXISTS_TAC [k; pc1; pc2; iv] THEN
     BETA_TAC THEN
     CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC])),
  (fun a b pc1 pc2 iv ->
    (MATCH_MP_TAC rth THEN
     MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; iv] THEN
     BETA_TAC THEN
     CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC])),
  (fun b a pc1 pc2 iv ->
    (MATCH_MP_TAC sth THEN
     MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; iv] THEN
     BETA_TAC THEN
     CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]));;

(* ------------------------------------------------------------------------- *)
(* Variants where there is an extra conjunct in the end state that may       *)
(* not hold at the outset of the zeroth iteration. This is mainly intended   *)
(* for cases where the last arithmetic operation sets flags that are then    *)
(* used to decide the branch.                                                *)
(* ------------------------------------------------------------------------- *)

let ENSURES_WHILE_PUP_TAC,ENSURES_WHILE_PDOWN_TAC,
    ENSURES_WHILE_PAUP_TAC,ENSURES_WHILE_PADOWN_TAC =
  let pth = prove
   (`!k pc1 pc2 p (q:num->A->bool).
       C ,, C = C /\
       ~(k = 0) /\
       ensures step (\s. program_decodes s /\
                         read pcounter s = word pc /\
                         precondition s)
                    (\s. program_decodes s /\
                         read pcounter s = word pc1 /\
                         p 0 s)
                    C /\
       (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  p i s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  p (i + 1) s /\ q (i + 1) s)
                             C) /\
       (!i. 0 < i /\ i < k /\ ~(i = k) /\ ~(i = 0) /\ ~(k = 0) /\ 0 < k
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  p i s /\ q i s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  p i s)
                             C) /\
       ensures step (\s. program_decodes s /\
                         read pcounter s = word pc2 /\
                         p k s /\ q k s)
                     postcondition
                     C
       ==> ensures step
             (\s. program_decodes s /\
                  read pcounter s = word pc /\
                  precondition s)
             postcondition
             C`,
    REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [IMP_CONJ] THEN
    DISCH_THEN(LABEL_TAC "*" o MATCH_MP
      (ONCE_REWRITE_RULE[IMP_CONJ] ENSURES_TRANS_SIMPLE)) THEN
    REWRITE_TAC[CONJ_ASSOC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    USE_THEN "*" (fun th ->
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] th)) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    USE_THEN "*" (fun th ->
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] th)) THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `~(k = 0) ==> k = (k - 1) + 1`)) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `~(k = 0) ==> k - 1 < k`)) THEN
    SPEC_TAC(`k - 1`,`j:num`) THEN MATCH_MP_TAC num_INDUCTION THEN
    ASM_REWRITE_TAC[ADD1] THEN CONJ_TAC THENL
     [STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `0` o CONJUNCT1) THEN
      ASM_ARITH_TAC;
      X_GEN_TAC `i:num`] THEN
    ASM_CASES_TAC `i + 1 < k` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `i + 1 < k ==> i < k`)) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "*" (fun th ->
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] th)) THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN (MP_TAC o SPEC `i + 1`)) THEN
    MATCH_MP_TAC(TAUT
     `(p /\ r) /\ (q /\ s ==> t) ==> (p ==> q) ==> (r ==> s) ==> t`) THEN
    ASM_REWRITE_TAC[ENSURES_TRANS_SIMPLE] THEN ASM_ARITH_TAC) in
  let qth = prove
   (`!k pc1 pc2 p (q:num->A->bool).
       C ,, C = C /\
       ~(k = 0) /\
       ensures step (\s. program_decodes s /\
                         read pcounter s = word pc /\
                         precondition s)
                    (\s. program_decodes s /\
                         read pcounter s = word pc1 /\
                         p k s)
                    C /\
       (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  p (i + 1) s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  p i s /\ q i s)
                             C) /\
       (!i. 0 < i /\ i < k /\ ~(i = k) /\ ~(i = 0) /\ ~(k = 0) /\ 0 < k
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  p i s /\ q i s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  p i s)
                             C) /\
       ensures step (\s. program_decodes s /\
                         read pcounter s = word pc2 /\
                         p 0 s /\ q 0 s)
                     postcondition
                     C
       ==> ensures step
             (\s. program_decodes s /\
                  read pcounter s = word pc /\
                  precondition s)
             postcondition
             C`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC[`k:num`; `pc1:num`; `pc2:num`;
                   `\i. (p:num->A->bool) (k - i)`;
                   `\i. (q:num->A->bool) (k - i)`] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[SUB_0; SUB_REFL] THEN
    REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN REWRITE_TAC[]) THENL
     [DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k - (i + 1)`) THEN
      ASM_SIMP_TAC[ARITH_RULE `i < k ==> k - (i + 1) + 1 = k - i`] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]) in
  let rth = prove
   (`!a b pc1 pc2 p (q:num->A->bool).
       C ,, C = C /\
       a < b /\
       ensures step (\s. program_decodes s /\
                         read pcounter s = word pc /\
                         precondition s)
                    (\s. program_decodes s /\
                         read pcounter s = word pc1 /\
                         p a s)
                    C /\
       (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  p i s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  p (i + 1) s /\ q (i + 1) s)
                             C) /\
       (!i. a < i /\ i < b /\ ~(i = b) /\ ~(i = 0) /\
            ~(i = a) /\ ~(b = 0) /\ 0 < b
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  p i s /\ q i s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  p i s)
                             C) /\
       ensures step (\s. program_decodes s /\
                         read pcounter s = word pc2 /\
                         p b s /\ q b s)
                     postcondition
                     C
       ==> ensures step
             (\s. program_decodes s /\
                  read pcounter s = word pc /\
                  precondition s)
             postcondition
             C`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`b - a:num`; `pc1:num`; `pc2:num`;
                   `\i. (p:num->A->bool) (a + i)`;
                   `\i. (q:num->A->bool) (a + i)`] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[ARITH_RULE `a:num < b ==> a + b - a = b`] THEN
    REWRITE_TAC[ADD_ASSOC] THEN
    CONJ_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC) in
  let sth = prove
   (`!a b pc1 pc2 p (q:num->A->bool).
       C ,, C = C /\
       a < b /\
       ensures step (\s. program_decodes s /\
                         read pcounter s = word pc /\
                         precondition s)
                    (\s. program_decodes s /\
                         read pcounter s = word pc1 /\
                         p b s)
                    C /\
       (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  p (i + 1) s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  p i s /\ q i s)
                             C) /\
       (!i. a < i /\ i < b /\ ~(i = a) /\ ~(i = 0) /\
            ~(i = b) /\ ~(b = 0) /\ 0 < b
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  p i s /\ q i s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  p i s)
                             C) /\
       ensures step (\s. program_decodes s /\
                         read pcounter s = word pc2 /\
                         p a s /\ q a s)
                     postcondition
                     C
       ==> ensures step
             (\s. program_decodes s /\
                  read pcounter s = word pc /\
                  precondition s)
             postcondition
             C`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [`b - a:num`; `pc1:num`; `pc2:num`;
                          `\i. (p:num->A->bool) (a + i)`;
                          `\i. (q:num->A->bool) (a + i)`] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[ARITH_RULE `a:num < b ==> a + b - a = b`] THEN
    REWRITE_TAC[ADD_ASSOC] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC) in
  (fun k pc1 pc2 pqiv ->
    let gvs,bods = strip_abs pqiv in
    let bodp,bodq = dest_conj bods in
    let piv = list_mk_abs(gvs,bodp)
    and qiv = list_mk_abs(gvs,bodq) in
    (MATCH_MP_TAC pth THEN
     MAP_EVERY EXISTS_TAC [k; pc1; pc2; piv; qiv] THEN
     BETA_TAC THEN
     CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC])),
  (fun k pc1 pc2 pqiv ->
    let gvs,bods = strip_abs pqiv in
    let bodp,bodq = dest_conj bods in
    let piv = list_mk_abs(gvs,bodp)
    and qiv = list_mk_abs(gvs,bodq) in
    (MATCH_MP_TAC qth THEN
     MAP_EVERY EXISTS_TAC [k; pc1; pc2; piv; qiv] THEN
     BETA_TAC THEN
     CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC])),
  (fun a b pc1 pc2 pqiv ->
    let gvs,bods = strip_abs pqiv in
    let bodp,bodq = dest_conj bods in
    let piv = list_mk_abs(gvs,bodp)
    and qiv = list_mk_abs(gvs,bodq) in
    (MATCH_MP_TAC rth THEN
     MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; piv; qiv] THEN
     BETA_TAC THEN
     CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC])),
  (fun b a pc1 pc2 pqiv ->
    let gvs,bods = strip_abs pqiv in
    let bodp,bodq = dest_conj bods in
    let piv = list_mk_abs(gvs,bodp)
    and qiv = list_mk_abs(gvs,bodq) in
    (MATCH_MP_TAC sth THEN
     MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; piv; qiv] THEN
     BETA_TAC THEN
     CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]));;

(* ------------------------------------------------------------------------- *)
(* A variant of the above WHILE loop tactics where the backedge-taken and    *)
(* untaken cases are combined. pc2 is supposed to be the destination PC when *)
(* the backedge is finally not taken.                                        *)
(* ------------------------------------------------------------------------- *)

let ENSURES_WHILE_UP2_TAC, ENSURES_WHILE_DOWN2_TAC,
    ENSURES_WHILE_AUP2_TAC, ENSURES_WHILE_ADOWN2_TAC =
  let pth = prove(
    `forall k pc1 pc2 (loopinv:num->A->bool) C precond postcond
        (pcounter:(A,(N)word)component).
      C ,, C = C /\ ~(k = 0) /\
      ensures step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precond s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinv 0 s)
        C /\
      (forall i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\
               loopinv i s)
          (\s. program_decodes s /\
               read pcounter s = word (if i + 1 < k then pc1 else pc2) /\
               loopinv (i + 1) s)
          C) /\
      ensures step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinv k s)
          postcond C
      ==>
      ensures step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precond s)
        postcond C`,
    REPEAT GEN_TAC THEN
    INTRO_TAC "HC HK HPRE HLOOP HPOST" THEN
    (* The post part *)
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
    USE_THEN "HC" (fun th -> REWRITE_TAC[th]) THEN
    META_EXISTS_TAC THEN CONJ_TAC THENL
    [ALL_TAC; USE_THEN "HPOST" (UNIFY_ACCEPT_TAC [`Q:A->bool`])] THEN
    REMOVE_THEN "HPOST" (K ALL_TAC) THEN
    (* The main loop + precond part *)
    (* Peel off the last iteration *)
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
    USE_THEN "HC" (fun th -> REWRITE_TAC[th]) THEN
    EXISTS_TAC `(\(s:A). program_decodes s /\
                         read pcounter s = (word pc1:(N)word) /\
                         loopinv (k - 1) s)` THEN
    CONJ_TAC THENL [
      ALL_TAC;
      USE_THEN "HLOOP" (fun th -> MP_TAC (SPEC `(k-1)` th)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `k - 1 + 1 = k` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC]
      THEN
      REWRITE_TAC[LT_REFL]
    ] THEN
    (* the main iterations *)
    SUBGOAL_THEN `k - 1 < k` MP_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
    SPEC_TAC (`k - 1`,`j:num`) THEN INDUCT_TAC THENL [
      ASM_REWRITE_TAC[] THEN NO_TAC;

      FIRST_X_ASSUM (fun th -> DISCH_TAC THEN MP_TAC th) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (LABEL_TAC "HPREVLOOP") THEN
      MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
      USE_THEN "HC" (fun th -> REWRITE_TAC[th]) THEN
      META_EXISTS_TAC THEN CONJ_TAC THENL
      [USE_THEN "HPREVLOOP" (UNIFY_ACCEPT_TAC [`Q:A->bool`]); ALL_TAC] THEN
      USE_THEN "HLOOP" (fun th -> MP_TAC (SPEC `j:num` th)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[GSYM ADD1] THEN NO_TAC
    ]) in
  let qth = prove(
    `forall k pc1 pc2 (loopinv:num->A->bool) precond postcond
        (pcounter:(A,(N)word)component).
      C ,, C = C /\ ~(k = 0) /\
      ensures step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precond s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinv k s)
        C /\
      (forall i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\
               loopinv (i + 1) s)
          (\s. program_decodes s /\
               read pcounter s = word (if i > 0 then pc1 else pc2) /\
               loopinv i s)
          C) /\
      ensures step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinv 0 s)
        postcond C
      ==>
      ensures step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precond s)
        postcond C`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `pc1:num`; `pc2:num`;
        `\i. (loopinv:num->A->bool) (k - i)`] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[SUB_0; SUB_REFL] THEN
    REPEAT (MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN REWRITE_TAC[]) THEN
    DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `k - (i + 1)`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE
      `i < k ==> k - (i + 1) + 1 = k - i /\ (k - (i + 1) > 0 <=> i + 1 < k)`]) in
  let rth = prove(
    `forall a b pc1 pc2 (loopinv:num->A->bool) precond postcond
        (pcounter:(A,(N)word)component).
      C ,, C = C /\ a < b /\
      ensures step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precond s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinv a s)
        C /\
      (forall i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\
               loopinv i s)
          (\s. program_decodes s /\
               read pcounter s = word (if i + 1 < b then pc1 else pc2) /\
               loopinv (i + 1) s)
          C) /\
      ensures step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinv b s)
        postcond C
      ==>
      ensures step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precond s)
        postcond C`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`b:num - a`; `pc1:num`; `pc2:num`;
        `\i. (loopinv:num->A->bool) (a + i)`] THEN
    ASM_REWRITE_TAC [SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC [ARITH_RULE `a:num < b ==> a + b - a = b`] THEN
    REWRITE_TAC [ADD_ASSOC] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `(a:num) + i`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(a + i) + 1 < b <=> i + 1 < b - a`]) in
  let sth = prove(
    `forall a b pc1 pc2 (loopinv:num->A->bool) precond postcond
        (pcounter:(A,(N)word)component).
      C ,, C = C /\ a < b /\
      ensures step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precond s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinv b s)
        C /\
      (forall i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\
               loopinv (i + 1) s)
          (\s. program_decodes s /\
               read pcounter s = word (if i > a then pc1 else pc2) /\
               loopinv i s)
          C) /\
      ensures step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinv a s)
        postcond C
      ==>
      ensures step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precond s)
        postcond C`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [`b:num - a`; `pc1:num`; `pc2:num`;
        `\i. (loopinv:num->A->bool) (a + i)`] THEN
    ASM_REWRITE_TAC [SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC [ARITH_RULE `a:num < b ==> a + b - a = b`] THEN
    REWRITE_TAC [ADD_ASSOC] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `(a:num) + i`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `a + i > a <=> i > 0`]) in
  (fun k pc1 pc2 iv ->
    MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [k; pc1; pc2; iv] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]),
  (fun k pc1 pc2 iv ->
    MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [k; pc1; pc2; iv] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]),
  (fun a b pc1 pc2 iv ->
    MATCH_MP_TAC rth THEN
    MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; iv] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]),
  (fun b a pc1 pc2 iv ->
    MATCH_MP_TAC sth THEN
    MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; iv] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Tactic to show |- ASSIGNS c subsumed ASSIGNS d for two components.        *)
(* Also allows the equality relation in place of "ASSIGNS c".                *)
(* ------------------------------------------------------------------------- *)

let SUBSUMED_ASSIGNS_TAC =
  MATCH_ACCEPT_TAC SUBSUMED_REFL ORELSE
  (MATCH_MP_TAC SUBSUMED_ID_EXTENSIONALLY_VALID_COMPONENT THEN
   CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV THEN NO_TAC) ORELSE
  CONV_TAC(BINOP_CONV(RAND_CONV COMPONENT_CANON_CONV)) THEN
  REPEAT(MATCH_MP_TAC SUBSUMED_ASSIGNS_SUBCOMPONENTS) THEN
  TRY(MATCH_ACCEPT_TAC SUBSUMED_ASSIGNS_SUBCOMPONENT) THEN
  GEN_REWRITE_TAC (BINOP_CONV o TRY_CONV)
   [ASSIGNS_BYTES8; ASSIGNS_BYTES16; ASSIGNS_BYTES32; ASSIGNS_BYTES64;
    ASSIGNS_BYTES128; ASSIGNS_BYTES256] THEN
  MATCH_MP_TAC SUBSUMED_ASSIGNS_BYTES THEN CONTAINED_TAC;;

(* ------------------------------------------------------------------------- *)
(* Tactic to show one MAYCHANGE list is subsumed by another.                 *)
(* ------------------------------------------------------------------------- *)

let SUBSUMED_MAYCHANGE_TAC =
  let lemma_step = prove
   (`(D ,, D = D ==> C1 subsumed D) /\
     (D ,, D = D ==> C2 subsumed D)
     ==> (D ,, D = D ==> (C1 ,, C2) subsumed D)`,
    MESON_TAC[SUBSUMED_FOR_SEQ])
  and lemma_start = prove
   (`D ,, D = D /\
     (D ,, D = D ==> C1 subsumed D) /\
     (D ,, D = D ==> C2 subsumed D)
    ==> (C1 ,, C2) subsumed D`,
    MESON_TAC[SUBSUMED_FOR_SEQ]) in
  let rec tac gl =
   ((MATCH_MP_TAC SUBSUMED_SEQ_LEFT THEN CONJ_TAC THENL
      [tac; SUBSUMED_ID_MAYCHANGE_TAC]) ORELSE
    (MATCH_MP_TAC SUBSUMED_SEQ_RIGHT THEN CONJ_TAC THENL
      [SUBSUMED_ID_MAYCHANGE_TAC; tac]) ORELSE
    SUBSUMED_ASSIGNS_TAC) gl in
  (* Anything is subsumed by (\s s'. true) *)
  MATCH_ACCEPT_TAC SUBSUMED_TRIVIAL ORELSE (
  CONV_TAC(BINOP_CONV MAYCHANGE_CANON_CONV) THEN
  TRY(MATCH_MP_TAC lemma_start THEN CONJ_TAC THENL
       [MAYCHANGE_IDEMPOT_TAC THEN NO_TAC; CONJ_TAC] THEN
      REPEAT(MATCH_MP_TAC lemma_step THEN CONJ_TAC) THEN
      DISCH_THEN(K ALL_TAC)) THEN
  ((POP_ASSUM_LIST(K ALL_TAC) THEN tac) ORELSE tac));;


(*** Example

g `(MAYCHANGE [X1] ,, MAYCHANGE [X2] ,,
    MAYCHANGE [memory :> bytes(a,2)]) subsumed
   (MAYCHANGE [CF; NF] ,, MAYCHANGE [X1; X2; X3] ,,
    MAYCHANGE [memory :> bytes64 a])`;;

e SUBSUMED_MAYCHANGE_TAC;;

***)

(* ------------------------------------------------------------------------- *)
(* Try to deduce a MAYCHANGE goal from a subsuming assumption.               *)
(* ------------------------------------------------------------------------- *)

let MONOTONE_MAYCHANGE_TAC =
  let pth = prove
   (`R s s' ==> R subsumed R' ==> R' s s'`,
    REWRITE_TAC[subsumed] THEN MESON_TAC[]) in
  FIRST_ASSUM
   (MATCH_MP_TAC o MATCH_MP pth o check (maychange_term o concl)) THEN
  REWRITE_TAC[ETA_AX] THEN SUBSUMED_MAYCHANGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Finalize the state, reshuffle and eliminate MAYCHANGE goals.              *)
(* ------------------------------------------------------------------------- *)

let ENSURES_FINAL_STATE_TAC =
  ENSURES_OR_ENSURES_N_TAC
      (GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ1_TAC)
      (GEN_REWRITE_TAC I [EVENTUALLY_N_TRIVIAL]) THEN
  GEN_REWRITE_TAC TRY_CONV [BETA_THM] THEN
  W(fun (asl,w) ->
        let onlycjs,othercjs = partition maychange_term (conjuncts w) in
        if othercjs = [] then
          TRY(REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC)
        else if onlycjs = [] then
          let w' = list_mk_conj othercjs in
          GEN_REWRITE_TAC I [CONJ_ACI_RULE(mk_eq(w,w'))]
        else
          let w' = mk_conj(list_mk_conj othercjs,list_mk_conj onlycjs) in
          (GEN_REWRITE_TAC I [CONJ_ACI_RULE(mk_eq(w,w'))] THEN
           TRY(CONJ_TAC THENL
                [ALL_TAC;
                 REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN
                 NO_TAC])));;

(* ------------------------------------------------------------------------- *)
(* Introduce a new ghost variable for a state component in "ensures".        *)
(* ------------------------------------------------------------------------- *)

let GHOST_INTRO_TAC =
  let pth = prove
   (`!f P step post frame.
         (!a. ensures step (\s. P s a /\ f s = a) post frame)
         ==> ensures step (\s. P s (f s)) post frame`,
    REPEAT GEN_TAC THEN REWRITE_TAC[ensures] THEN
    GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
    REWRITE_TAC[IMP_CONJ_ALT; FORALL_UNWIND_THM1]) in
  let pth_n = prove
   (`forall f (P:S->A->bool) step post frame n.
         (!a. ensures_n step (\s. P s a /\ f s = a) post frame n)
         ==> ensures_n step (\s. P s (f s)) post frame n`,
    REPEAT GEN_TAC THEN REWRITE_TAC[ensures_n] THEN
    GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
    REWRITE_TAC[IMP_CONJ_ALT; FORALL_UNWIND_THM1]) in
  fun t comp ->
    ENSURES_OR_ENSURES_N_TAC
        (MP_TAC(ISPEC comp pth))
        (MP_TAC(ISPEC comp pth_n)) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BETA_CONV)) THEN
    DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC t THEN
    ENSURES_OR_ENSURES_N_TAC
        (GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ABS_CONV o TOP_DEPTH_CONV)
          [GSYM CONJ_ASSOC])
        (GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o LAND_CONV o ABS_CONV o
                          TOP_DEPTH_CONV)
          [GSYM CONJ_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Turn the bits of the precondition not depending on state into asms        *)
(* ------------------------------------------------------------------------- *)

let ENSURES_CONSTANT_PRECONDITION = prove
 (`!step p (q:A->bool) r.
        ensures step (\s. p) q r <=> p ==> ensures step (\s. T) q r`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p:bool` THEN
  ASM_REWRITE_TAC[ENSURES_TRIVIAL]);;

let ENSURES_CONSTANT_PRECONDITION_CONJUNCTS = prove
 (`(!step p p' (q:A->bool) r.
        ensures step (\s. p /\ p' s) q r <=>
        p ==> ensures step (\s. p' s) q r) /\
   (!step p p' (q:A->bool) r.
        ensures step (\s. p' s /\ p) q r <=>
        p ==> ensures step (\s. p' s) q r)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p:bool` THEN
  ASM_REWRITE_TAC[ENSURES_TRIVIAL]);;

let (GLOBALIZE_PRECONDITION_TAC:tactic) =
  let tac1 =
      ENSURES_OR_ENSURES_N_TAC
          (GEN_REWRITE_TAC I [ENSURES_CONSTANT_PRECONDITION])
          (GEN_REWRITE_TAC I [ENSURES_N_CONSTANT_PRECONDITION])
      THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)
  and tac2 =
      ENSURES_OR_ENSURES_N_TAC
          (GEN_REWRITE_TAC I
              [CONJUNCT2 ENSURES_CONSTANT_PRECONDITION_CONJUNCTS])
          (GEN_REWRITE_TAC I
              [CONJUNCT2 ENSURES_N_CONSTANT_PRECONDITION_CONJUNCTS])
      THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) in
  fun (_,w as gl) ->
    let mom,nstep =
        ensures_or_ensures_n
          w
          (fun () -> (w,w))(*nstep will not be used when ensures*)
          (fun () -> dest_comb w)
        () in
    let pap,fra = dest_comb mom in
    let enp,pos = dest_comb pap in
    let ens,pre = dest_comb enp in
    let sv,pbod = dest_abs pre in
    let cjs1,cjs2 = partition (free_in sv) (conjuncts pbod) in
    if cjs1 = [] then tac1 gl else if cjs2 = [] then ALL_TAC gl else
    let th1 = CONJ_ACI_RULE
     (mk_eq(pbod,mk_conj(list_mk_conj cjs1,list_mk_conj cjs2))) in
    let th2 =
        ensures_or_ensures_n
          w
          (fun () -> AP_THM (AP_THM (AP_TERM ens (ABS sv th1)) pos) fra)
          (fun () -> AP_THM (AP_THM (AP_THM (AP_TERM ens (ABS sv th1)) pos)
              fra) nstep)
        () in
    (CONV_TAC(K th2) THEN tac2) gl;;

(* ------------------------------------------------------------------------- *)
(* A way of using a lemma for a subroutine or subcomponent.                  *)
(* Tactic supports the basic templating and leaves two user subgoals.        *)
(* ------------------------------------------------------------------------- *)

let ENSURES_SUBLEMMA_THM = prove
 (`!t (P:A->bool) Q R.
        (!s. P s ==> P' s) /\
        R' subsumed R /\
        (!s s'. P s /\ Q' s' /\ R' s s' ==> Q s')
        ==> ensures t P' Q' R' ==> ensures t P Q R`,
  REPEAT GEN_TAC THEN REWRITE_TAC[subsumed] THEN STRIP_TAC THEN
  REWRITE_TAC[ensures] THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `s:A` THEN DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM]
        EVENTUALLY_MONO) THEN
  ASM_MESON_TAC[]);;

let ENSURES_SUBLEMMA_TAC execth s0 s1 =
  MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [W(fun (asl,w) -> X_GEN_TAC(mk_var(s0,type_of(fst(dest_forall w))))) THEN
    STRIP_TAC;
    CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC THEN NO_TAC; ALL_TAC] THEN
    W(fun (asl,w) -> X_GEN_TAC(mk_var(s0,type_of(fst(dest_forall w))))) THEN
    W(fun (asl,w) -> X_GEN_TAC(mk_var(s1,type_of(fst(dest_forall w))))) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
    CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    NONSELFMODIFYING_STATE_UPDATE_TAC execth THEN
    ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC)];;

(*** A version that also tries nonmodification for subroutines ***)

let ENSURES_SUBSUBLEMMA_TAC (execth::subths) s0 s1 =
  MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [W(fun (asl,w) -> X_GEN_TAC(mk_var(s0,type_of(fst(dest_forall w))))) THEN
    STRIP_TAC;
    CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC THEN NO_TAC; ALL_TAC] THEN
    W(fun (asl,w) -> X_GEN_TAC(mk_var(s0,type_of(fst(dest_forall w))))) THEN
    W(fun (asl,w) -> X_GEN_TAC(mk_var(s1,type_of(fst(dest_forall w))))) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
    CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    NONSELFMODIFYING_STATE_UPDATE_TAC execth THEN
    MAP_EVERY (TRY o NONSELFMODIFYING_STATE_UPDATE_TAC) subths THEN
    ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC)];;

(* ------------------------------------------------------------------------- *)
(* Scrub a "preserved" component from the MAYCHANGE list.                    *)
(* ------------------------------------------------------------------------- *)

let ENSURES_MAYCHANGE_PRESERVED = prove
 (`!(c:(A,B)component) t P Q R.
        extensionally_valid_component c /\
        (!s s'. R s s' ==> read c s' = read c s) /\
        (!d. ensures t (\s. P s /\ read c s = d)
                       (\s. Q s /\ read c s = d)
                       (R ,, MAYCHANGE [c]))
        ==> ensures t P Q R`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures; EXTENSIONALLY_VALID_COMPONENT] THEN
  STRIP_TAC THEN X_GEN_TAC `s0:A` THEN DISCH_TAC THEN
  ABBREV_TAC `d = read (c:(A,B)component) s0` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`d:B`; `s0:A`]) THEN
  ASM_REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
  REWRITE_TAC[ASSIGNS_THM; seq] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s0:A`) THEN
  ABBREV_TAC `fr = (R:A->A->bool) s0` THEN DISCH_TAC THEN
  SPEC_TAC(`s0:A`,`s0:A`) THEN MATCH_MP_TAC EVENTUALLY_MONO THEN
  X_GEN_TAC `s2:A` THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `s1:A` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_TAC `y:B`) THEN
  ASM_MESON_TAC[]);;

let ENSURES_PRESERVED_TAC pname ctm =
  MATCH_MP_TAC(ISPEC ctm ENSURES_MAYCHANGE_PRESERVED) THEN
  CONJ_TAC THENL [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV; ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
    CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV
     COMPONENT_READ_OVER_WRITE_ORTHOGONAL_CONV)) THEN
    REFL_TAC;
    REWRITE_TAC[GSYM CONJ_ASSOC; GSYM SEQ_ASSOC] THEN
    W(fun (asl,w) -> X_GEN_TAC(mk_var(pname,type_of(fst(dest_forall w)))))];;

let ENSURES_MAYCHANGE_EXISTING_PRESERVED = prove
 (`!(c:(A,B)component) d t P Q R.
        extensionally_valid_component c /\
        (!s s'. R s s' ==> read c s' = read c s) /\
        (!s. P s ==> read c s = d) /\
        ensures t P (\s. Q s /\ read c s = d) (R ,, MAYCHANGE [c])
        ==> ensures t P Q R`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENSURES_MAYCHANGE_PRESERVED THEN
  EXISTS_TAC `c:(A,B)component` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q <=> ~(p ==> ~q)`] THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `e:B` THEN
  ASM_CASES_TAC `e:B = d` THEN
  ASM_REWRITE_TAC[NOT_IMP; ENSURES_TRIVIAL; ETA_AX]);;

let ENSURES_EXISTING_PRESERVED_TAC ctm =
  W(fun (asl,w) ->
        MATCH_MP_TAC(ISPEC ctm ENSURES_MAYCHANGE_EXISTING_PRESERVED) THEN
        EXISTS_TAC(rand(find (fun e -> is_eq e && free_in ctm (lhand e))
                             (conjuncts(body(lhand(rator w))))))) THEN
  CONJ_TAC THENL [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV; ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
    CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV
     COMPONENT_READ_OVER_WRITE_ORTHOGONAL_CONV)) THEN
    REFL_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    REWRITE_TAC[GSYM CONJ_ASSOC; GSYM SEQ_ASSOC]];;

(* ------------------------------------------------------------------------- *)
(* A more refined version where we are allowed to modify a high part.        *)
(* ------------------------------------------------------------------------- *)

let ASSIGNS_TOPHALF_BOTTOMHALF = prove
 (`!c:(A,(N tybit0)word)component.
        valid_component c
        ==> ASSIGNS (c :> tophalf) ,, ASSIGNS (c :> bottomhalf) = ASSIGNS c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ASSIGNS; ASSIGNS_SEQ; FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:A`; `s':A`] THEN
  REWRITE_TAC[assign; WRITE_COMPONENT_COMPOSE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[valid_component]) THEN
  ASM_REWRITE_TAC[READ_WRITE_TOPHALF_BOTTOMHALF] THEN
  EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM; RIGHT_IMP_EXISTS_THM] THENL
   [MAP_EVERY X_GEN_TAC [`x:N word`; `y:N word`] THEN
    EXISTS_TAC `(word_join:N word->N word->(N tybit0)word) x y`;
    X_GEN_TAC `z:(N tybit0)word` THEN MAP_EVERY EXISTS_TAC
     [`word_subword (z:(N tybit0)word) (dimindex(:N),dimindex(:N)):N word`;
      `word_subword (z:(N tybit0)word) (0,dimindex(:N)):N word`]] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SPEC_TAC(`read (c:(A,(N tybit0)word)component) s`,`w:(N tybit0) word`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN GEN_TAC THEN
  GEN_REWRITE_TAC I [GSYM READ_TOPHALF_BOTTOMHALF_EQ] THEN
  REWRITE_TAC[READ_WRITE_TOPHALF_BOTTOMHALF] THEN
  REWRITE_TAC[bottomhalf; tophalf; subword; read] THEN
  SIMP_TAC[VAL_WORD_JOIN; word_subword; EXP; DIV_1] THEN
  REWRITE_TAC[DIMINDEX_TYBIT0; DIV_MOD; GSYM EXP_ADD; GSYM MULT_2] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN; ARITH_RULE `MIN (2 * n) n = n`] THEN
  REWRITE_TAC[MOD_MULT_ADD; WORD_VAL; ARITH_RULE `MIN n n = n`;
              VAL_MOD_REFL] THEN
  REWRITE_TAC[MULT_2; EXP_ADD; GSYM DIV_MOD] THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ; DIV_LT; VAL_BOUND] THEN
  REWRITE_TAC[ADD_CLAUSES; VAL_MOD_REFL; WORD_VAL]);;

let ENSURES_MAYCHANGE_TOPHALF_PRESERVED = prove
 (`!(c:(A,((N)tybit0)word)component) t P Q R.
        valid_component c /\
        (!s s'. R s s' ==> read c s' = read c s) /\
        (!d. ensures t (\s. P s /\ read (c :> bottomhalf) s = d)
                       (\s. Q s /\ read (c :> bottomhalf) s = d)
                       (R ,, MAYCHANGE [c]))
        ==> ensures t P Q (R ,, MAYCHANGE [c :> tophalf])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures; valid_component] THEN
  STRIP_TAC THEN X_GEN_TAC `s0:A` THEN DISCH_TAC THEN
  ABBREV_TAC `d = read (c:(A,((N)tybit0)word)component) s0` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`word_subword (d:((N)tybit0)word) (0,dimindex(:N)):N word`; `s0:A`]) THEN
  ASM_REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN ANTS_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; SEQ_ID] THEN
    ASM_REWRITE_TAC[bottomhalf; READ_SUBWORD];
    ALL_TAC] THEN
  REWRITE_TAC[ASSIGNS_THM; seq] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s0:A`) THEN
  ABBREV_TAC `fr = (R:A->A->bool) s0` THEN DISCH_TAC THEN
  SPEC_TAC(`s0:A`,`s0:A`) THEN MATCH_MP_TAC EVENTUALLY_MONO THEN
  X_GEN_TAC `s2:A` THEN ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `s1:A` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_TAC `y:((N)tybit0)word`) THEN
  EXISTS_TAC `s1:A` THEN ASM_REWRITE_TAC[WRITE_COMPONENT_COMPOSE] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SYM o SYM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN EXISTS_TAC `read tophalf (y:(N tybit0)word)` THEN
  ASM_SIMP_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [GSYM READ_TOPHALF_BOTTOMHALF_EQ] THEN
  ASM_REWRITE_TAC[READ_WRITE_TOPHALF_BOTTOMHALF] THEN
  REWRITE_TAC[bottomhalf; read; subword; GSYM word_subword]);;

(* ------------------------------------------------------------------------- *)
(* A kind of dual of ignoring things about unchanged components.             *)
(* ------------------------------------------------------------------------- *)

let ENSURES_FORGET_COMPONENTS_TAC =
  let lemma = prove
   (`!p' q'. ensures step p' q' c /\
             (!s. p s ==> p' s) /\ (!s s'. p s /\ q' s' /\ c s s' ==> q s')
             ==> ensures step p q c`,
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN STRIP_TAC THEN
    MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN
    ASM_REWRITE_TAC[SUBSUMED_REFL]) in
  let lemma_n = prove
   (`!p' q'. ensures_n step p' q' c n /\
             (!s. p s ==> p' s) /\ (!s s'. p s /\ q' s' /\ c s s' ==> q s')
             ==> ensures_n step p q c n`,
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN STRIP_TAC THEN
    MATCH_MP_TAC ENSURES_N_SUBLEMMA_THM THEN
    ASM_REWRITE_TAC[SUBSUMED_REFL]) in
  fun ctm ->
    let rec funch tm =
      match tm with
        Comb(Const("read",_),c) -> mem c ctm
      | Comb(s,t) -> funch s && funch t
      | Abs(x,t) -> funch t
      | Const("bytes_loaded",_) -> false
      | Const("aligned_bytes_loaded",_) -> false
      | _ -> true in
    fun (_,w as gl) ->
      let mom,nsteps = ensures_or_ensures_n
          w
          (fun () -> (w,w)) (* nsteps will be ignored when ensures *)
          (fun () -> dest_comb w)
          () in
      let pap,fra = dest_comb mom in
      let enp,pos = dest_comb pap in
      let ens,pre = dest_comb enp in
      let sv,pbod = dest_abs pre in
      let tv,qbod = dest_abs pos in
      let pcjs = filter (not o funch) (conjuncts pbod)
      and qcjs = filter (not o funch) (conjuncts qbod) in
     (ENSURES_OR_ENSURES_N_TAC
        (MATCH_MP_TAC lemma)
        (MATCH_MP_TAC lemma_n) THEN
      EXISTS_TAC(mk_abs(sv,list_mk_conj pcjs)) THEN
      EXISTS_TAC(mk_abs(tv,list_mk_conj qcjs)) THEN
      CONJ_TAC THENL
       [ALL_TAC;
        CONJ_TAC THENL
         [REWRITE_TAC[] THEN GEN_TAC THEN STRIP_TAC THEN
          ASM_REWRITE_TAC[] THEN NO_TAC;
          REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
          REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2
           (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) MP_TAC)) THEN
          REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
          REWRITE_TAC[GSYM SEQ_ASSOC] THEN
          PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
          CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
          REWRITE_TAC[ASSIGNS_THM] THEN
          REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
          ASSUMPTION_STATE_UPDATE_TAC THEN ASM_REWRITE_TAC[] THEN
          NO_TAC]]) gl;;

(* ------------------------------------------------------------------------- *)
(* Organize a sequence of writes into canonical form.                        *)
(* ------------------------------------------------------------------------- *)

type unwrapper = Unwrapper of bool * thm * (term -> unwrapper);;

(* Select the named byte view from the value width, then instantiate the
   polymorphic alias theorem from the concrete wbytes term. A conversion must
   return an equation whose left side is exactly its input, including the
   address type. *)
let WBYTES_ALIAS_CONV =
  let pth8 = SYM BYTES8_WBYTES
  and pth16 = SYM BYTES16_WBYTES
  and pth32 = SYM BYTES32_WBYTES
  and pth64 = SYM BYTES64_WBYTES in
  TRY_CONV (fun tm ->
    match tm with
    | Const("wbytes",Tyapp(_,[Tyapp(_,[_]);Tyapp(_,[_;Tyapp(_,[N])])])) ->
        let pth = match Num.int_of_num (dest_finty N) with
        | 8 -> pth8
        | 16 -> pth16
        | 32 -> pth32
        | 64 -> pth64
        | _ -> fail () in
        PART_MATCH lhand pth tm
    | _ -> fail ());;

let component_alias_conv = ref ALL_CONV;;

(* * WRITE_MERGE_CONV normalizes terms of the form `write c y (f s)`, where
     `f s` is a normalized write-tree such as
      `(modify registers (write (element (word 0)) a o
                          write (element (word 1)) b) o
        write PC pc) s`.
     Calling WRITE_MERGE_CONV recursively on iterative `write` expressions can
     be used to construct such trees. Here `c` must be canonicalized, but may
     be a composition of basic components.
   * READ_WRITE_CONV works on terms of the form `read c (f s)` where `c` is
     canonicalized and `f s` is a normalized write-tree, and will simplify them
     to some written value `a`, or to `read c s` if the writes do not affect
     the given component.
   * READ_WRITE_UPDATER `f s = s'`, where `f s` is a normalized write-tree,
     constructs a list of proofs of `f s = s' |- read c s' = a` for all written
     components in `f`, as well as a function that will turn
     `A |- read c s = x` into `A, f s = s' |- read c s' = x'`, where
     `x'` is either `x`, if the component was not modified, or `a` for some
     written value `a`. `c` need not be canonicalized, and it will be
     aliased in the result theorem. *)
let (WRITE_MERGE_CONV:conv), (READ_WRITE_CONV:conv),
    (READ_WRITE_UPDATER:term -> thm list * (thm -> bool * thm)) =
  let dest_modifier = function
  | Comb(Comb(Const("write",_),c),_) -> c
  | Comb(Comb(Const("modify",_),c),_) -> c
  | _ -> failwith "dest_modifier" in
  let rec dest_modifiers = function
  | Comb(Comb(Const("o",_),m),l) -> dest_modifier m :: dest_modifiers l
  | m -> [dest_modifier m] in

  let unseq =
    let conv1 = REWR_CONV (SPEC_ALL WRITE_COMPOSE) in
    let rec unseq t = TRY_CONV (conv1 THENC RAND_CONV unseq) t in
    function
    | Comb(Comb(Const("o",_),_),_) as t -> LAND_CONV unseq t
    | t -> unseq t in
  let pth_mm = GSYM (SPEC_ALL MODIFY_o)
  and pth_mw = SPEC_ALL MODIFY_o_WRITE
  and pth_wm = SPEC_ALL WRITE_o_MODIFY
  and pth_ww = SPEC_ALL WRITE_o_WRITE
  and swap_conv =
    let mco = prove
      (`(P ==> f1 o g1 = f2 o g2) ==> P ==> f1 o g1 o h = f2 o g2 o h`,
        REWRITE_TAC [o_ASSOC] THEN MESON_TAC[]) in
    let net = itlist
      ((fun th -> net_of_conv (lhs (rand (concl th))) (IMP_REWR_CONV th)) o
      MATCH_MP mco o SPEC_ALL)
      [MODIFY_SYM; MODIFY_WRITE_SYM; WRITE_MODIFY_SYM; WRITE_SYM]
      empty_net in
    REWRITES_CONV net
  and conv_assoc = REWR_CONV (SPEC_ALL o_ASSOC) in
  let rec merge_conv t =
    let c::cs = dest_modifiers t in
    if mem c cs then
      try
        let conv = match lhand t with
        | Comb(Comb(Const("write",_),c),_) ->
          let cth = C MP (WEAKLY_VALID_COMPONENT_RULE c) in
          (cth o IMP_REWR_CONV pth_wm) ORELSEC (cth o IMP_REWR_CONV pth_ww)
        | Comb(Comb(Const("modify",_),c),_) ->
          let cth = C MP (STRONGLY_VALID_COMPONENT_RULE c) in
          (cth o IMP_REWR_CONV pth_mm) ORELSEC
          ((cth o IMP_REWR_CONV pth_mw) THENC RAND_CONV merge_conv)
        | _ -> failwith "WRITE_MERGE_CONV" in
        let rec push_conv (c'::cs) t = if c = c' then
          (if cs = [] then conv else conv_assoc THENC LAND_CONV conv) t
        else
          ((C MP (ORTHOGONAL_COMPONENTS_RULE2 c c') o swap_conv) THENC
            RAND_CONV (push_conv cs)) t in
        push_conv cs t
      with Failure _ -> REFL t
    else REFL t in
  let conv = RATOR_CONV (unseq THENC merge_conv) in
  let o_conv = REWR_CONV (SYM (SPEC_ALL o_THM)) in
  let WRITE_MERGE_CONV t = match t with
  | Comb(Comb(Comb(Const("write",_),c),x),Comb(f,_))
    when can dest_modifiers f -> (o_conv THENC conv) t
  | Comb(Comb(Comb(Const("write",_),_),_),_) -> conv t
  | _ -> failwith "WRITE_MERGE_CONV" in

  let pth_rw = SPEC_ALL READ_WRITE_VALID_COMPONENT
  and pth_rm = SPEC_ALL READ_MODIFY_VALID_COMPONENT
  and conv_rwo = PART_MATCH (lhs o rand)
    (SPEC_ALL READ_WRITE_ORTHOGONAL_COMPONENTS)
  and conv_rmo = PART_MATCH (lhs o rand)
    (SPEC_ALL READ_MODIFY_ORTHOGONAL_COMPONENTS)
  and conv_odef = RAND_CONV (REWR_CONV (SPEC_ALL o_THM)) in
  let rec read_conv c cs t = match cs with
  | [] -> REFL t
  | c'::cs when c = c' ->
    let cth = C MP (VALID_COMPONENT_RULE c) in
    let conv =
       (cth o PART_MATCH (lhs o rand) pth_rw) ORELSEC
      ((cth o PART_MATCH (lhs o rand) pth_rm) THENC
       RAND_CONV (read_conv c cs)) in
    (if cs = [] then conv else conv_odef THENC conv) t
  | c'::cs ->
    let cth = C MP (ORTHOGONAL_COMPONENTS_RULE2 c c') in
    let conv =
     ((cth o conv_rwo) ORELSEC (cth o conv_rmo)) THENC read_conv c cs in
    (if cs = [] then conv else conv_odef THENC conv) t in
  let convco1,convco2 =
    let pth = SPEC_ALL READ_COMPONENT_COMPOSE in
    REWR_CONV pth, REWR_CONV (SYM pth) in
  let rec READ_WRITE_CONV t = match t with
  | Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),_),_)),_) ->
    (convco1 THENC RAND_CONV READ_WRITE_CONV THENC
     READ_WRITE_CONV THENC TRY_CONV convco2) t
  | Comb(Comb(Const("read",_),_),Comb(Comb(Const("read",_),_),_)) ->
    TRY_CONV (RAND_CONV (CHANGED_CONV READ_WRITE_CONV) THENC READ_WRITE_CONV) t
  | Comb(Comb(Const("read",_),c),Comb(f,_)) ->
    (match catch dest_modifiers f with
    | None -> REFL t
    | Some cs -> read_conv c cs t)
  | Comb(Comb(Const("read",_),_),_) -> REFL t
  | _ -> failwith "READ_WRITE_CONV" in

  let read_c = `read c:S->V` in
  let o_conv = REWR_CONV (SPEC_ALL o_THM) in
  let rec mk_unwrap b th = Unwrapper (b, th, app_unwrap b th)
  and app_unwrap b th t = mk_unwrap b (AP_TERM t th) in
  let alias_conv = REPEATC convco2 THENC function
  | Comb(Comb(Const("read",_),_),_) as t -> LAND_CONV !component_alias_conv t
  | t -> ALL_CONV t in
  let READ_WRITE_UPDATER t =
    let s,s2 = dest_eq t in
    let f,s = dest_comb s in
    let rec mk_updater hs th =
      let th = match rand (rhs (concl th)) with
      | Comb(Comb(Comb(Const("o",_),_),_),_) ->
        CONV_RULE (RAND_CONV (RAND_CONV o_conv)) th
      | _ -> th in
      let mkth c = match type_of c with
      | Tyapp(_,[S;V]) as ty -> (S,V),
        itlist (PROVE_HYP o ORTHOGONAL_COMPONENTS_RULE2 c) hs
          (INST [c,mk_var ("c",ty)] (INST_TYPE [V,`:V`] th))
      | _ -> fail () in
      let t = rhs (concl th) in
      match rand t with
      | Comb(Comb(Comb(Const("write",_),c),y),s) ->
        let (S,V),th1 = mkth c in
        let pth = PINST [S,`:S`; V,`:V`]
          [c,`c:(S,V)component`; y,`y:V`; s,`s:S`] pth_rw in
        let th1 = TRANS th1 (MP pth (VALID_COMPONENT_RULE c)) in
        let ls, up = mk_updater (c::hs) (TRANS th (UNDISCH (conv_rwo t))) in
        th1::ls, fun d -> if c = d then mk_unwrap true th1 else up d
      | Comb(Comb(Comb(Const("modify",_),c),f),s) ->
        let (S,V),th1 = mkth c in
        let pth = PINST [S,`:S`; V,`:V`]
          [c,`c:(S,V)component`; f,`f:V->V`; s,`s:S`] pth_rm in
        let th1 = CONV_RULE (RAND_CONV (RAND_CONV READ_WRITE_CONV))
          (TRANS th1 (MP pth (VALID_COMPONENT_RULE c))) in
        let ls1, up1 = mk_updater [] (AP_TERM (inst [V,`:S`] read_c) th1) in
        let ls, up = mk_updater (c::hs) (TRANS th (UNDISCH (conv_rmo t))) in
        ls1 @ ls, fun d ->
          if c = d then Unwrapper (true, th1, up1 o rand) else up d
      | s -> [], mk_unwrap false o snd o mkth in
    let ls, up = mk_updater []
      (AP_TERM (inst [type_of s,`:S`] read_c) (SYM (ASSUME t))) in
    map (CONV_RULE (BINOP_CONV alias_conv)) ls,
    fun th -> match lhs (concl th) with
    | Comb(Comb(Const("read",_),c),s') as t when s' = s ->
      let rec unwrap = function
      | Comb(f,(Comb(Comb(Const("read",_),c),s') as x)) ->
        let Unwrapper(_,_,g) = unwrap x in g f
      | Comb(Comb(Const("read",_),c),_) -> up c
      | _ -> failwith "READ_WRITE_UPDATER unwrap" in
      let th1 = (LAND_CONV COMPONENT_CANON_CONV THENC REPEATC convco1) t in
      let Unwrapper(b,th2,_) = unwrap (rhs (concl th1)) in
      let th3 = CONV_RULE (LAND_CONV alias_conv) th2 in
      b, if b then th3 else TRANS th3 (TRANS (SYM th1) th)
    | _ -> failwith "READ_WRITE_UPDATER: conv not applicable" in

  WRITE_MERGE_CONV, READ_WRITE_CONV, READ_WRITE_UPDATER;;

let WRITE_SIMPLIFY_CONV =
  let conv =
    let net = itlist (net_of_thm false)
     (prove (`write (rvalue c) y = I`,
        REWRITE_TAC[FUN_EQ_THM; I_THM; WRITE_RVALUE]) ::
      prove (`modify (rvalue c) f = I`,
        REWRITE_TAC[modify; WRITE_RVALUE; I_DEF]) ::
      CONJUNCTS (SPEC_ALL I_O_ID)) empty_net in
    let th = SPEC_ALL MODIFY_ID in
    let net = net_of_conv (lhs (rand (concl th))) (fun t -> MP
      (IMP_REWR_CONV th t)
      (EXTENSIONALLY_VALID_COMPONENT_RULE (lhand t))) net in
    REWRITES_CONV net in
  fun (asl:(string*thm) list) -> DEPTH_CONV conv;;

let (ASM_READ_TCL:term->thm_tactic->tactic) =
  let pth = GSYM EXISTS_REFL in
  function
  | Comb(Comb(Const("read",_),_),_) as t ->
    let th = LAND_CONV !component_alias_conv t in
    (match rhs (concl th) with
    | Comb(Comb(_,Comb(Const("rvalue",_),c)),s) ->
      let th' = TRANS th (PINST [type_of c,`:V`; type_of s,`:S`]
        [c,`c:V`; s,`s:S`] READ_RVALUE) in
      fun ttac -> ttac th'
    | t' -> fun ttac (asl,_ as g) ->
      match catch (tryfind (fun _,h -> TRANS th h)) asl with
      | Some th -> ttac th g
      | None -> CHOOSE_THEN (fun th' ->
          ASSUME_TAC th' THEN ttac (TRANS th th')) (ISPEC t' pth) g)
  | t -> fun G -> G (REFL t);;

(* VIA_CONV sym `R ,, A` will prove `R ,, A subsumes S` for some normalized
  VIA-tree `S`, when `R` is a normalized VIA-tree. This can also be used to
  normalize an arbitrary relation `A` by taking `R` to be `(=)`, which is the
  empty normalized VIA-tree. When `sym` is true, it will attempt to reorder
  state components in A to match elements in R, while if `sym` is false it will
  assume that no reordering of state components is necessary in `A` to
  normalize it into `R`.

  A normalized VIA-tree is a left associated list (((=) ,, R1) ,, .. Rn) where
  each Ri is either `ASSIGNS c` or `VIA c A` where A is recursively a
  normalized VIA-tree, and the `c`'s are orthogonal strong state components.
  This representation mirrors the modify/write trees used for data carrying,
  but here we only track which state components are modified. *)
let (VIA_CONV:bool->conv) =
  let pth_mc0 = REWR_CONV (prove (`R ,, MAYCHANGE [] = R`,
    REWRITE_TAC [MAYCHANGE; SEQ_ID]))
  and pth_mc1 = REWR_CONV (prove
   (`R ,, MAYCHANGE (CONS c cs) = (R ,, ASSIGNS c) ,, MAYCHANGE cs`,
    REWRITE_TAC [MAYCHANGE; SEQ_ASSOC]))
  and pth_lid = REWR_CONV (SYM (SPEC_ALL (CONJUNCT1 SEQ_ID)))
  and pth_rid = REWR_CONV (SPEC_ALL (CONJUNCT2 SEQ_ID))
  and pth_a2 = REWR_CONV (SYM (SPEC_ALL VIA_ASSIGNS))
  and pth_aa = IMP_REWR_CONV (prove
   (`strongly_valid_component c ==>
     (R ,, ASSIGNS c) ,, ASSIGNS c = R ,, ASSIGNS c`,
    IMP_REWRITE_TAC [GSYM SEQ_ASSOC; ASSIGNS_ABSORB_SAME_COMPONENTS;
      STRONGLY_VALID_IMP_VALID_COMPONENT;
      VALID_IMP_WEAKLY_VALID_COMPONENT]))
  and pth_vv = IMP_REWR_CONV (prove
   (`strongly_valid_component c ==>
     (R ,, VIA c A) ,, VIA c B = R ,, VIA c (A ,, B)`,
    IMP_REWRITE_TAC [SEQ_ASSOC; GSYM VIA_ASSIGNS; VIA_SEQ]))
  and pth_va,pth_av =
    let f tm = PART_MATCH (lhand o rand) (prove (tm,
      REWRITE_TAC [GSYM SEQ_ASSOC] THEN DISCH_THEN (fun th ->
        MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC [SUBSUMED_REFL] THEN
        MATCH_MP_TAC SUBSUMED_FOR_SEQ THEN
        IMP_REWRITE_TAC [SUBSUMED_REFL; ASSIGNS_ABSORB_SAME_COMPONENTS;
          STRONGLY_VALID_IMP_VALID_COMPONENT; VIA_SUBSUMED_ASSIGNS;
          VALID_IMP_WEAKLY_VALID_COMPONENT; th]))) in
    f `strongly_valid_component c ==>
      (R ,, VIA c A) ,, ASSIGNS c subsumed R ,, ASSIGNS c`,
    f `strongly_valid_component c ==>
      (R ,, ASSIGNS c) ,, VIA c A subsumed R ,, ASSIGNS c`
  and pth_assoc = REWR_CONV (SPEC_ALL SEQ_ASSOC)
  and pth_saa = IMP_REWR_CONV (prove
   (`orthogonal_components c d ==>
     (R ,, ASSIGNS c) ,, ASSIGNS d = (R ,, ASSIGNS d) ,, ASSIGNS c`,
    IMP_REWRITE_TAC [GSYM SEQ_ASSOC; ASSIGNS_SWAP_ORTHOGONAL_COMPONENTS]))
  and pth_sva = IMP_REWR_CONV (prove
   (`orthogonal_components c d ==>
     (R ,, VIA c A) ,, ASSIGNS d = (R ,, ASSIGNS d) ,, VIA c A`,
    IMP_REWRITE_TAC [GSYM SEQ_ASSOC; VIA_ASSIGNS_SYM]))
  and pth_sav = IMP_REWR_CONV (prove
   (`orthogonal_components c d ==>
     (R ,, ASSIGNS c) ,, VIA d B = (R ,, VIA d B) ,, ASSIGNS c`,
    IMP_REWRITE_TAC [GSYM SEQ_ASSOC; ASSIGNS_VIA_SYM]))
  and pth_svv = IMP_REWR_CONV (prove
   (`orthogonal_components c d ==>
     (R ,, VIA c A) ,, VIA d B = (R ,, VIA d B) ,, VIA c A`,
    IMP_REWRITE_TAC [GSYM SEQ_ASSOC; VIA_SYM])) in

  let rec contains c = function
  | Comb(Comb(Const(",,",_),fs),f) ->
    (match f with
    | Comb(Const("ASSIGNS",_),c') -> c = c'
    | Comb(Comb(Const("VIA",_),c'),_) -> c = c'
    | _ -> failwith "VIA_WRITE_RULE: contains") ||
    contains c fs
  | _ -> false in

  let via_match = function
  | Comb(Const("ASSIGNS",_),c) -> c, false
  | Comb(Comb(Const("VIA",_),c),_) -> c, true
  | _ -> failwith "VIA_CONV" in

  let to_subsumed =
    let pth = MESON [SUBSUMED_REFL] `A = B ==> A subsumed B` in
    fun th -> if is_eq (concl th) then MATCH_MP pth th else th in
  let LAND_CONV' =
    let pth = (UNDISCH o MESON [SUBSUMED_SEQ; SUBSUMED_REFL])
      `(R:S->S->bool) subsumed S ==> (R ,, A:S->S->bool) subsumed (S ,, A)` in
    fun conv -> function
    | Comb(Comb((Const(",,",_) as f),R),A) ->
      let th = conv R in
      if is_eq (concl th) then AP_THM (AP_TERM f th) A else
      let S = rand (concl th) and sty = fst (dest_fun_ty (type_of R)) in
      PROVE_HYP th (PINST [sty,`:S`] [R,`R:S->S->bool`;
        S,`S:S->S->bool`; A,`A:S->S->bool`] pth)
    | _ -> failwith "VIA_CONV: LAND_CONV'" in
  let RAND_CONV_VIA' =
    let pth = (UNDISCH o MESON [SUBSUMED_SEQ; SUBSUMED_REFL; SUBSUMED_VIA])
      `(A:V->V->bool) subsumed B ==>
       (R:S->S->bool) ,, VIA c A subsumed R ,, VIA c B` in
    fun conv -> function
    | Comb((Comb(Const(",,",_),R) as f),
        Comb((Comb(Const("VIA",_),c) as g),A)) ->
      let th = conv A in
      if is_eq (concl th) then AP_TERM f (AP_TERM g th) else
      let B = rand (concl th)
      and sty = fst (dest_fun_ty (type_of A))
      and vty = fst (dest_fun_ty (type_of R)) in
      PROVE_HYP th (PINST [sty,`:S`; vty,`:V`] [R,`R:S->S->bool`;
        c,`c:(S,V)component`; A,`A:V->V->bool`; B,`B:V->V->bool`] pth)
    | _ -> failwith "VIA_CONV: RAND_CONV_VIA'" in
  let CONV_RHS_RULE' =
    let pth = (UNDISCH_ALL o MESON [subsumed])
      `(A:S->S->bool) subsumed B ==> B subsumed C ==> A subsumed C` in
    fun conv th ->
      let B = rand (concl th) in
      let th2 = conv B in
      if is_eq (concl th) && is_eq (concl th2) then TRANS th th2 else
      let A = lhand (concl th) and C = rand (concl th2)
      and sty = fst (dest_fun_ty (type_of B)) in
      PROVE_HYP (to_subsumed th) (PROVE_HYP (to_subsumed th2)
        (PINST [sty,`:S`]
          [A,`A:S->S->bool`; B,`B:S->S->bool`; C,`C:S->S->bool`] pth)) in
  let THENC' c1 c2 = CONV_RHS_RULE' c2 o c1 in

  fun sym ->
    let rec VIA_CONV t = match rand t with
    | Const("=",_) -> pth_rid t
    | Comb(Comb(Const(",,",_),_),_) ->
      (THENC' pth_assoc (THENC' (LAND_CONV' VIA_CONV) VIA_CONV)) t
    | Comb(Const("MAYCHANGE",_),Const("NIL",_)) -> pth_mc0 t
    | Comb(Const("MAYCHANGE",_),Comb(Comb(Const("CONS",_),_),_)) ->
      (THENC' (pth_mc1 THENC LAND_CONV (RAND_CONV COMPONENT_CANON_CONV))
        (THENC' (LAND_CONV' VIA_CONV) VIA_CONV)) t
    | Comb(Const("ASSIGNS",_),Comb(Comb(Const(":>",_),_),_)) ->
      (THENC' (RAND_CONV pth_a2) VIA_CONV) t
    | c -> push sym (via_match c) t
    and push sym (c,cv) t =
      if sym && contains c (lhand t) then
        let rec swaps t =
          match catch (via_match o rand) (lhand t) with
          | Some(d, dv) when c <> d ->
            let pth = if dv then
              if cv then pth_svv t else pth_sva t else
              if cv then pth_sav t else pth_saa t in
            CONV_RHS_RULE' (LAND_CONV' swaps)
              (MP pth (ORTHOGONAL_COMPONENTS_RULE2 d c))
          | _ -> conv_at sym c cv t in
        swaps t
      else conv_at sym c cv t
    and conv_at sym c cv t =
      match catch (fun t ->
        let d,dv = via_match (rand t) in
        if c = d then dv, STRONGLY_VALID_COMPONENT_RULE c
        else fail ()) (lhand t) with
      | None -> (match rand t with
        | Comb(Comb(Const("VIA",_),_),_) ->
          RAND_CONV_VIA' (THENC' pth_lid VIA_CONV) t
        | _ -> REFL t)
      | Some (dv, cth) ->
        match dv, cv with
        | false, false -> MP (pth_aa t) cth
        | false, true -> MP (pth_av t) cth
        | true, false -> MP (pth_va t) cth
        | true, true ->
          CONV_RHS_RULE' (RAND_CONV_VIA' VIA_CONV) (MP (pth_vv t) cth) in
    to_subsumed o VIA_CONV;;

(* VIA_WRITE_RULE `|- R s0 s1` `f` will prove `|- S s0 (f s1)` for some
  normalized VIA-tree `S`, when `R` is a normalized VIA-tree and `f` is a
  normalized write tree. *)
let VIA_WRITE_RULE =
  let pth_m = (UNDISCH_ALL o prove)
   (`R (s0:S) (s1:S) ==> A (read c s1:V) (f (read c s1)) ==>
     R ,, VIA c A subsumed S ==> S s0 (modify c f s1)`,
    REWRITE_TAC [seq; VIA; subsumed; assign; modify] THEN MESON_TAC[])
  and pth_w = (UNDISCH_ALL o prove)
   (`R (s0:S) (s1:S) ==>
     R ,, ASSIGNS c subsumed S ==> S s0 (write c (y:V) s1)`,
    REWRITE_TAC [seq; subsumed; ASSIGNS; assign] THEN MESON_TAC[])
  and pth_co = REWR_CONV (SYM (SPEC_ALL o_THM)) in

  let rec VIA_WRITE_RULE th sf = match concl th, sf with
  | _, Comb(Comb(Const("o",_),f),g) ->
    CONV_RULE (RAND_CONV pth_co) (VIA_WRITE_RULE (VIA_WRITE_RULE th g) f)
  | Comb(Comb(R,s0),s1), Comb(Comb(Const("modify",_),c),f) ->
    let th2 = VIA_WRITE_RULE (REFL (list_mk_icomb "read" [c; s1])) f in
    let A = rator (rator (concl th2)) in
    let th3 = VIA_CONV true
      (list_mk_icomb ",," [R; list_mk_icomb "VIA" [c; A]]) in
    let S = rand (concl th3) in
    let pth = PINST [type_of s0,`:S`; fst (dest_fun_ty (type_of f)),`:V`]
      [c,`c:(S,V)component`; s0,`s0:S`; s1,`s1:S`; f,`f:V->V`;
       R,`R:S->S->bool`; S,`S:S->S->bool`; A,`A:V->V->bool`] pth_m in
    PROVE_HYP th (PROVE_HYP th2 (PROVE_HYP th3 pth))
  | Comb(Comb(R,s0),s1), Comb(Comb(Const("write",_),c),y) ->
    let th2 = VIA_CONV true
      (list_mk_icomb ",," [R; list_mk_icomb "ASSIGNS" [c]]) in
    let S = rand (concl th2) in
    let pth = PINST [type_of s0,`:S`; type_of y,`:V`]
      [c,`c:(S,V)component`; s0,`s0:S`; s1,`s1:S`; y,`y:V`;
       R,`R:S->S->bool`; S,`S:S->S->bool`] pth_w in
    PROVE_HYP th (PROVE_HYP th2 pth)
  | _ -> failwith "VIA_WRITE_RULE" in
  VIA_WRITE_RULE;;

(* MAYCHANGE_WRITE_RULE `|- R s0 s1` `f` will prove `|- S s0 (f s1)` for some
  MAYCHANGE list `S`, when `R` is a MAYCHANGE list (or VIA-tree) and `f` is a
  normalized write tree. *)
let MAYCHANGE_WRITE_RULE =
  let to_via =
    let pth = (UNDISCH_ALL o prove)
      (`(=) ,, R subsumed S ==> R (s0:S) (s1:S) ==> S s0 s1`,
        REWRITE_TAC [SEQ_ID; subsumed] THEN METIS_TAC[])
    and mkeq = curry mk_icomb `(,,) (=)` in
    fun th -> match concl th with
    | Comb(Comb(R,s0),s1) ->
      let th2 = VIA_CONV false (mkeq R) in
      let S = rand (concl th2) in
      PROVE_HYP th (PROVE_HYP th2 (PINST [type_of s0,`:S`]
        [s0,`s0:S`; s1,`s1:S`; R,`R:S->S->bool`; S,`S:S->S->bool`] pth))
    | _ -> failwith "MAYCHANGE_WRITE_RULE: to_via" in

  let from_via =
    let pth0 = prove (`(=) = MAYCHANGE ([]:((S,V)component)list)`,
      REWRITE_TAC[MAYCHANGE])
    and conv =
      REDEPTH_CONV (REWRITES_CONV (itlist (uncurry net_of_conv)
       [`(=) ,, R`,REWR_CONV (SPEC_ALL (CONJUNCT1 SEQ_ID));
        `VIA c (A ,, B)`,
          (fun th ->
            MP th (STRONGLY_VALID_COMPONENT_RULE (rand (lhand (concl th))))) o
          IMP_REWR_CONV (SPEC_ALL VIA_SEQ);
        `VIA c (ASSIGNS A)`,REWR_CONV (SPEC_ALL VIA_ASSIGNS)]
        (basic_net()))) THENC
      ONCE_DEPTH_CONV (function
      | Comb(Const("ASSIGNS",_),_) as t -> RAND_CONV !component_alias_conv t
      | _ -> fail ()) THENC
      REWRITE_CONV
       [SYM (SPEC_ALL SEQ_ASSOC); SYM (SPEC_ALL MAYCHANGE_SING);
        SYM (REWRITE_RULE [GSYM MAYCHANGE_SING] (CONJUNCT2 MAYCHANGE))] in
    function
    | Const("=",Tyapp(_,[S;_])) -> INST_TYPE [S,`:S`] pth0
    | t -> conv t in

  fun th sf -> CONV_RULE
    (RATOR_CONV (RATOR_CONV from_via)) (VIA_WRITE_RULE (to_via th) sf);;


(* ------------------------------------------------------------------------- *)
(* Prove ensures_n from ensures.                                             *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_ENSURES_TAC th =
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_N_ENSURES THEN META_EXISTS_TAC THEN
  MP_TAC (SPEC_ALL th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN (UNIFY_ACCEPT_TAC [`f_n:armstate->num`]);;


(* ------------------------------------------------------------------------- *)
(* Induction, basically a variant of the usual WHILE rule with a             *)
(* test at the end. Versions for up from 0...k-1, down from k-1...0 and up   *)
(* from a...b-1.                                                             *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_WHILE_UP_TAC, ENSURES_N_WHILE_DOWN_TAC,
    ENSURES_N_WHILE_AUP_TAC, ENSURES_N_WHILE_ADOWN_TAC =
  let pth = prove(
    `!k pc1 pc2 (loopinvariant:num->A->bool) nsteps_pre f_nsteps nsteps_back nsteps_post.
      C ,, C = C /\ ~(k = 0) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant 0 s)
        C (\s. nsteps_pre) /\
      (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant (i + 1) s)
          C (\s. f_nsteps i)) /\
      (!i. 0 < i /\ i < k /\ ~(i = k) /\ ~(i = 0) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          C (\s. nsteps_back)) /\
      ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant k s)
          postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum (0..(k-1)) (\i. f_nsteps i) + (k-1) * nsteps_back) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN
    CHOOSE_THEN ASSUME_TAC (GSYM (ISPEC `nsum (0..(k-1)) (\i. f_nsteps i) + (k-1) * nsteps_back` EXISTS_REFL)) THEN
    IMP_REWRITE_TAC [ENSURES_N_TRANS_SIMPLE] THEN
    UNDISCH_THEN `nsum (0..k - 1) (\i. f_nsteps i) + (k - 1) * nsteps_back = x` (fun th -> REWRITE_TAC [SYM th]) THEN
    FIRST_ASSUM (SUBST1_TAC o MATCH_MP (ARITH_RULE `~(k = 0) ==> k = (k - 1) + 1`)) THEN
    UNDISCH_THEN `~(k = 0)` (MP_TAC o MATCH_MP (ARITH_RULE `~(k = 0) ==> k - 1 < k`)) THEN
    SPEC_TAC (`k-1:num`,`j:num`) THEN
    REWRITE_TAC [ARITH_RULE `(j + 1) - 1 = j`] THEN
    INDUCT_TAC THENL [
      STRIP_TAC THEN REWRITE_TAC [NSUM_SING_NUMSEG; ADD_0; MULT] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o SPEC `0`) THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC [NSUM_CLAUSES_NUMSEG; ADD1; ARITH_RULE `0 <= j + 1`] THEN
      ASM_REWRITE_TAC [ARITH_RULE `(nsum (0..j) (\i. f_nsteps i) + f_nsteps (j + 1)) + (j + 1) * nsteps_back = (nsum (0..j) (\i. f_nsteps i) + (j * nsteps_back)) + f_nsteps (j + 1) + nsteps_back`] THEN
      STRIP_TAC THEN
      MATCH_MP_TAC ENSURES_N_TRANS_SIMPLE THEN META_EXISTS_TAC THEN
      ASM_REWRITE_TAC [] THEN
      CONJ_TAC THENL [
        UNDISCH_THEN `j + 1 < k` (MP_TAC o MP (ARITH_RULE `j + 1 < k ==> j < k`)) THEN
        FIRST_X_ASSUM (UNIFY_ACCEPT_TAC [`Q:A->bool`]);
        SUBST1_TAC (ARITH_RULE `((f_nsteps (j + 1)):num) + nsteps_back = nsteps_back + f_nsteps (j + 1)`) THEN
        MATCH_MP_TAC ENSURES_N_TRANS_SIMPLE THEN META_EXISTS_TAC THEN
        ASM_REWRITE_TAC [] THEN
        CONJ_TAC THENL [
          UNDISCH_THEN `j + 1 < k` (MP_TAC o MP (ARITH_RULE `j + 1 < k ==> 0 < j + 1 /\ j + 1 < k /\ ~(j + 1 = k) /\ ~(j + 1 = 0) /\ ~(k = 0) /\ 0 < k`)) THEN
          FIRST_X_ASSUM (UNIFY_ACCEPT_TAC [`Q:A->bool`] o SPEC `j + 1`);
          UNDISCH_THEN `j + 1 < k` (MP_TAC o MP (ARITH_RULE `j + 1 < k ==> j + 1 < k /\ ~(j + 1 = k) /\ ~(k = 0) /\ 0 < k`)) THEN
          FIRST_X_ASSUM (UNIFY_ACCEPT_TAC [`Q:A->bool`] o SPEC `j + 1`)]]]) in
  let qth = prove(
    `!k pc1 pc2 (loopinvariant:num->A->bool) nsteps_pre f_nsteps nsteps_back nsteps_post.
      C ,, C = C /\ ~(k = 0) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant k s)
        C (\s. nsteps_pre) /\
      (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant (i + 1) s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant i s)
          C (\s. f_nsteps i)) /\
      (!i. 0 < i /\ i < k /\ ~(i = k) /\ ~(i = 0) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          C (\s. nsteps_back)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant 0 s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum (0..(k-1)) (\i. f_nsteps i) + (k-1) * nsteps_back) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `pc1:num`; `pc2:num`; `\i. (loopinvariant:num->A->bool) (k - i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (k - (i + 1))`; `nsteps_back:num`; `nsteps_post:num`] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[SUB_0; SUB_REFL] THEN
    REPEAT (MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN REWRITE_TAC[]) THENL [
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `k - (i + 1)`) THEN
      ASM_SIMP_TAC [ARITH_RULE `i < k ==> k - (i + 1) + 1 = k - i`] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC [ARITH_RULE `k - (i + 1) = (k - 1) - i`; NSUM_REFLECT'; ETA_AX]]) in
  let rth = prove(
    `!a b pc1 pc2 (loopinvariant:num->A->bool) nsteps_pre f_nsteps nsteps_back nsteps_post.
      C ,, C = C /\ a < b /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant a s)
        C (\s. nsteps_pre) /\
      (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant (i + 1) s)
          C (\s. f_nsteps i)) /\
      (!i. a < i /\ i < b /\ ~(i = b) /\ ~(i = 0) /\ ~(i = a) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          C (\s. nsteps_back)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant b s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum(a..(b-1)) (\i. f_nsteps i) + (b-1-a) * nsteps_back) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`b - a:num`; `pc1:num`; `pc2:num`; `\i. (loopinvariant:num->A->bool) (a + i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (a + i)`; `nsteps_back:num`; `nsteps_post:num`] THEN
    ASM_REWRITE_TAC [SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC [ARITH_RULE `a:num < b ==> a + b - a = b`] THEN
    REWRITE_TAC [ADD_ASSOC] THEN REPEAT STRIP_TAC THENL [
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC [ARITH_RULE `b - a - 1 = b - 1 - a`] THEN
      ONCE_ASM_REWRITE_TAC [MATCH_MP NSUM_OFFSET_0 (MP
          (ARITH_RULE `a:num < b ==> a <= b - 1`) (ASSUME `a:num < b`))] THEN
      ASM_REWRITE_TAC [ADD_SYM]]) in
  let sth = prove(
    `!a b pc1 pc2 (loopinvariant:num->A->bool) nsteps_pre f_nsteps nsteps_back nsteps_post.
      C ,, C = C /\ a < b /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant b s)
        C (\s. nsteps_pre) /\
      (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant (i + 1) s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant i s)
          C (\s. f_nsteps i)) /\
      (!i. a < i /\ i < b /\ ~(i = a) /\ ~(i = 0) /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          C (\s. nsteps_back)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant a s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum(a..(b-1)) (\i. f_nsteps i) + (b-1-a) * nsteps_back) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [`b - a:num`; `pc1:num`; `pc2:num`; `\i. (loopinvariant:num->A->bool) (a + i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (a + i)`; `nsteps_back:num`; `nsteps_post:num`] THEN
    ASM_REWRITE_TAC [SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC [ARITH_RULE `a:num < b ==> a + b - a = b`] THEN
    REWRITE_TAC [ADD_ASSOC] THEN REPEAT STRIP_TAC THENL [
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC [ARITH_RULE `b - a - 1 = b - 1 - a`] THEN
      ONCE_ASM_REWRITE_TAC [MATCH_MP NSUM_OFFSET_0 (MP (ARITH_RULE `a < b ==> a <= b - 1`) (ASSUME `a:num < b`))] THEN
      ASM_REWRITE_TAC [ADD_SYM]]) in
  (fun k pc1 pc2 iv f_nsteps nsteps_pre nsteps_back nsteps_post ->
    MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [k; pc1; pc2; iv; nsteps_pre; f_nsteps; nsteps_back; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]),
  (fun k pc1 pc2 iv f_nsteps nsteps_pre nsteps_back nsteps_post ->
    MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [k; pc1; pc2; iv; nsteps_pre; f_nsteps; nsteps_back; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]),
  (fun a b pc1 pc2 iv f_nsteps nsteps_pre nsteps_back nsteps_post ->
    MATCH_MP_TAC rth THEN
    MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; iv; nsteps_pre; f_nsteps; nsteps_back; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]),
  (fun b a pc1 pc2 iv f_nsteps nsteps_pre nsteps_back nsteps_post ->
    MATCH_MP_TAC sth THEN
    MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; iv; nsteps_pre; f_nsteps; nsteps_back; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* (ensures_n)                                                               *)
(* Variants where there is an extra conjunct in the end state that may       *)
(* not hold at the outset of the zeroth iteration. This is mainly intended   *)
(* for cases where the last arithmetic operation sets flags that are then    *)
(* used to decide the branch.                                                *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_WHILE_PUP_TAC,ENSURES_N_WHILE_PDOWN_TAC,
    ENSURES_N_WHILE_PAUP_TAC,ENSURES_N_WHILE_PADOWN_TAC =
  let pth = prove(
    `!k pc1 pc2 p (q:num->A->bool) nsteps_pre f_nsteps nsteps_post.
      C ,, C = C /\ ~(k = 0) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ p 0 s)
        C (\s. nsteps_pre) /\
      (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p i s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p (i + 1) s /\ q (i + 1) s)
          C (\s. f_nsteps i)) /\
      (!i. 0 < i /\ i < k /\ ~(i = k) /\ ~(i = 0) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p i s /\ q i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p i s)
          C (\s. 1)) /\
      ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p k s /\ q k s)
          postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum (0..(k-1)) (\i. f_nsteps i) + (k-1)) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN
    CHOOSE_THEN ASSUME_TAC (GSYM (ISPEC `nsum (0..(k-1)) (\i. f_nsteps i) + (k-1)` EXISTS_REFL)) THEN
    IMP_REWRITE_TAC [ENSURES_N_TRANS_SIMPLE] THEN
    UNDISCH_THEN `nsum (0..k - 1) (\i. f_nsteps i) + k - 1 = x` (fun th -> REWRITE_TAC [SYM th]) THEN
    FIRST_ASSUM (SUBST1_TAC o MATCH_MP (ARITH_RULE `~(k = 0) ==> k = (k - 1) + 1`)) THEN
    UNDISCH_THEN `~(k = 0)` (MP_TAC o MATCH_MP (ARITH_RULE `~(k = 0) ==> k - 1 < k`)) THEN
    SPEC_TAC (`k-1:num`,`j:num`) THEN
    REWRITE_TAC [ARITH_RULE `(j + 1) - 1 = j`] THEN
    INDUCT_TAC THENL [
      STRIP_TAC THEN REWRITE_TAC [NSUM_SING_NUMSEG; ADD_0] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o SPEC `0`) THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC [NSUM_CLAUSES_NUMSEG; ADD1; ARITH_RULE `0 <= j + 1`] THEN
      ASM_REWRITE_TAC [ARITH_RULE `(nsum (0..j) (\i. f_nsteps i) + f_nsteps (j + 1)) + j + 1 = (nsum (0..j) (\i. f_nsteps i) + j) + f_nsteps (j + 1) + 1`] THEN
      STRIP_TAC THEN
      MATCH_MP_TAC ENSURES_N_TRANS_SIMPLE THEN META_EXISTS_TAC THEN
      ASM_REWRITE_TAC [] THEN
      CONJ_TAC THENL [
        UNDISCH_THEN `j + 1 < k` (MP_TAC o MP (ARITH_RULE `j + 1 < k ==> j < k`)) THEN
        FIRST_X_ASSUM (UNIFY_ACCEPT_TAC [`Q:A->bool`]);
        SUBST1_TAC (ARITH_RULE `f_nsteps (j + 1) + 1 = 1 + f_nsteps (j + 1)`) THEN
        MATCH_MP_TAC ENSURES_N_TRANS_SIMPLE THEN META_EXISTS_TAC THEN
        ASM_REWRITE_TAC [] THEN
        CONJ_TAC THENL [
          UNDISCH_THEN `j + 1 < k` (MP_TAC o MP (ARITH_RULE `j + 1 < k ==> 0 < j + 1 /\ j + 1 < k /\ ~(j + 1 = k) /\ ~(j + 1 = 0) /\ ~(k = 0) /\ 0 < k`)) THEN
          FIRST_X_ASSUM (UNIFY_ACCEPT_TAC [`Q:A->bool`] o SPEC `j + 1`);
          UNDISCH_THEN `j + 1 < k` (MP_TAC o MP (ARITH_RULE `j + 1 < k ==> j + 1 < k /\ ~(j + 1 = k) /\ ~(k = 0) /\ 0 < k`)) THEN
          FIRST_X_ASSUM (UNIFY_ACCEPT_TAC [`Q:A->bool`] o SPEC `j + 1`)]]]) in
  let qth = prove(
    `!k pc1 pc2 p (q:num->A->bool) nsteps_pre f_nsteps nsteps_post.
      C ,, C = C /\ ~(k = 0) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ p k s)
        C (\s. nsteps_pre) /\
      (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p (i + 1) s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p i s /\ q i s)
          C (\s. f_nsteps i)) /\
      (!i. 0 < i /\ i < k /\ ~(i = k) /\ ~(i = 0) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p i s /\ q i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p i s)
          C (\s. 1)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ p 0 s /\ q 0 s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum (0..(k-1)) (\i. f_nsteps i) + (k-1)) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `pc1:num`; `pc2:num`; `\i. (p:num->A->bool) (k - i)`; `\i. (q:num->A->bool) (k - i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (k - (i + 1))`; `nsteps_post:num`] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[SUB_0; SUB_REFL] THEN
    REPEAT (MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN REWRITE_TAC[]) THENL [
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `k - (i + 1)`) THEN
      ASM_SIMP_TAC [ARITH_RULE `i < k ==> k - (i + 1) + 1 = k - i`] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC [ARITH_RULE `k - (i + 1) = (k - 1) - i`; NSUM_REFLECT'; ETA_AX]]) in
  let rth = prove(
    `!a b pc1 pc2 p (q:num->A->bool) nsteps_pre f_nsteps nsteps_post.
      C ,, C = C /\ a < b /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ p a s)
        C (\s. nsteps_pre) /\
      (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p i s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p (i + 1) s /\ q (i + 1) s)
          C (\s. f_nsteps i)) /\
      (!i. a < i /\ i < b /\ ~(i = b) /\ ~(i = 0) /\ ~(i = a) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p i s /\ q i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p i s)
          C (\s. 1)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ p b s /\ q b s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum(a..(b-1)) (\i. f_nsteps i) + (b-1-a)) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`b - a:num`; `pc1:num`; `pc2:num`; `\i. (p:num->A->bool) (a + i)`; `\i. (q:num->A->bool) (a + i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (a + i)`; `nsteps_post:num`] THEN
    ASM_REWRITE_TAC [SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC [ARITH_RULE `a:num < b ==> a + b - a = b`] THEN
    REWRITE_TAC [ADD_ASSOC] THEN REPEAT STRIP_TAC THENL [
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC [ARITH_RULE `b - a - 1 = b - 1 - a`] THEN
      ONCE_ASM_REWRITE_TAC [MATCH_MP NSUM_OFFSET_0 (MP (ARITH_RULE `a < b ==> a <= b - 1`)
          (ASSUME `a:num < b`))] THEN
      ASM_REWRITE_TAC [ADD_SYM]]) in
  let sth = prove(
    `!a b pc1 pc2 p (q:num->A->bool) nsteps_pre f_nsteps nsteps_post.
      C ,, C = C /\ a < b /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ p b s)
        C (\s. nsteps_pre) /\
      (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p (i + 1) s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p i s /\ q i s)
          C (\s. f_nsteps i)) /\
      (!i. a < i /\ i < b /\ ~(i = a) /\ ~(i = 0) /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p i s /\ q i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p i s)
          C (\s. 1)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ p a s /\ q a s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum(a..(b-1)) (\i. f_nsteps i) + (b-1-a)) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [`b - a:num`; `pc1:num`; `pc2:num`; `\i. (p:num->A->bool) (a + i)`; `\i. (q:num->A->bool) (a + i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (a + i)`; `nsteps_post:num`] THEN
    ASM_REWRITE_TAC [SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC [ARITH_RULE `a:num < b ==> a + b - a = b`] THEN
    REWRITE_TAC [ADD_ASSOC] THEN REPEAT STRIP_TAC THENL [
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC [ARITH_RULE `b - a - 1 = b - 1 - a`] THEN
      ONCE_ASM_REWRITE_TAC [MATCH_MP NSUM_OFFSET_0 (MP (ARITH_RULE `a < b ==> a <= b - 1`)
          (ASSUME `a:num < b`))] THEN
      ASM_REWRITE_TAC [ADD_SYM]]) in
  (fun k pc1 pc2 p q f_nsteps nsteps_pre nsteps_post ->
    MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [k; pc1; pc2; p; q; nsteps_pre; f_nsteps; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]),
  (fun k pc1 pc2 p q f_nsteps nsteps_pre nsteps_post ->
    MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [k; pc1; pc2; p; q; nsteps_pre; f_nsteps; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]),
  (fun a b pc1 pc2 p q f_nsteps nsteps_pre nsteps_post ->
    MATCH_MP_TAC rth THEN
    MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; p; q; nsteps_pre; f_nsteps; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]),
  (fun b a pc1 pc2 p q f_nsteps nsteps_pre nsteps_post ->
    MATCH_MP_TAC sth THEN
    MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; p; q; nsteps_pre; f_nsteps; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]);;
