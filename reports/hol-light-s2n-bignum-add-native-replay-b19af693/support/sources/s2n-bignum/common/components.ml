(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(*                General theory of state components.                        *)
(*                                                                           *)
(* Core component infrastructure (type, read/write, validity, orthogonality, *)
(* composition, records) is now provided by HOL Light's Library/components.ml *)
(* and Library/records.ml. This file adds s2n-bignum-specific extensions.    *)
(* ========================================================================= *)

needs "Library/words.ml";;
needs "common/overlap.ml";;
needs "Library/components.ml";;

let components_print_log = ref false;;

(* ------------------------------------------------------------------------- *)
(* Additional composition theorems.                                          *)
(* ------------------------------------------------------------------------- *)

let READ_WRITE_COMPONENT_COMPOSE_GEN2 = prove
 (`!f sc1 sc2.
        (!y s. read sc1 (write sc1 y s) = y) /\
        (!y s. read sc2 (write sc2 y s) = f y)
        ==> !y s. read (sc1 :> sc2) (write (sc1 :> sc2) y s) = f y`,
  SIMP_TAC[READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE]);;

let READ_WRITE_COMPONENT_COMPOSE_CONDITIONAL = prove
 (`!sc1 sc2.
        (!y s. read sc1 (write sc1 y s) = y) /\
        (!y s. read sc2 (write sc2 y (read sc1 s)) = y)
        ==> !y s. read (sc1 :> sc2) (write (sc1 :> sc2) y s) = y`,
  SIMP_TAC[READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE]);;

let READ_WRITE_ORTHOGONAL_COMPOSE_L = prove
 (`!c1 c2 f.
        (!y s. read c1 (write c1 y s) = y) /\
        (!y s. read c2 (write c2 y s) = f y)
        ==> !y s. read (c1 :> c2) (write (c1 :> c2) y s) = f y`,
  REWRITE_TAC[FORALL_COMPONENT; component_compose; read; write; o_THM] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Additional read-versus-write compose theorems.                            *)
(* ------------------------------------------------------------------------- *)

let WEAK_READ_OVER_WRITE = prove
 (`!c:(S,A)component.
        weak_read_over_write c <=>
        !y s s'. read c (write c y s) = read c (write c y s')`,
  REWRITE_TAC[weak_read_over_write] THEN
  REWRITE_TAC[GSYM SKOLEM_THM] THEN MESON_TAC[]);;

let READ_OVER_WRITE_COMPOSE = prove
 (`!(c:(A,B)component) (d:(B,C)component).
        read_over_write c /\ read_over_write d
        ==> read_over_write(c :> d)`,
  REWRITE_TAC[read_over_write] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  MESON_TAC[]);;

let WRITE_OVER_READ_COMPOSE = prove
 (`!(c:(A,B)component) (d:(B,C)component).
        write_over_read c /\ write_over_read d
        ==> write_over_read(c :> d)`,
  REWRITE_TAC[write_over_read] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  MESON_TAC[]);;

let WRITE_OVER_WRITE_COMPOSE = prove
 (`!(c:(A,B)component) (d:(B,C)component).
        read_over_write c /\
        write_over_write c /\ write_over_write d
        ==> write_over_write(c :> d)`,
  REWRITE_TAC[read_over_write; write_over_write] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  MESON_TAC[]);;

let WEAK_READ_OVER_WRITE_COMPOSE = prove
 (`!(c:(A,B)component) (d:(B,C)component).
        read_over_write c /\ weak_read_over_write d
        ==> weak_read_over_write(c :> d)`,
  REWRITE_TAC[read_over_write; WEAK_READ_OVER_WRITE] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Additional valid component theorems.                                      *)
(* ------------------------------------------------------------------------- *)

let VALID_COMPONENT_UNWAP = prove
 (`!c:(S,A)component.
        valid_component c <=>
        read_over_write c /\ write_over_write c`,
  REWRITE_TAC[valid_component; read_over_write; write_over_write]);;

let READ_WRITE_VALID_COMPONENT = prove
 (`!c y s. valid_component c ==> read c (write c (y:V) (s:S)) = y`,
  SIMP_TAC[valid_component]);;

(* ------------------------------------------------------------------------- *)
(* Additional weakly valid component theorems.                               *)
(* ------------------------------------------------------------------------- *)

let WEAKLY_VALID_COMPONENT_UNWAP = prove
 (`!c:(S,A)component.
        weakly_valid_component c <=>
        weak_read_over_write c /\ write_over_write c`,
  REWRITE_TAC[weakly_valid_component;
              weak_read_over_write; write_over_write]);;

let WEAKLY_VALID_COMPONENT = prove
 (`!c. weakly_valid_component c <=>
        (!y s s'. read c (write c y s) = read c (write c y s')) /\
        (!y z s. write c z (write c y s) = write c z s)`,
  REWRITE_TAC[weakly_valid_component] THEN
  REWRITE_TAC[GSYM SKOLEM_THM] THEN MESON_TAC[]);;

let WEAKLY_VALID_COMPONENT_COMPOSE = prove
 (`!c d. valid_component c /\
         weakly_valid_component d
         ==> weakly_valid_component (c :> d)`,
  SIMP_TAC[valid_component; weakly_valid_component;
           READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  MESON_TAC[]);;

let WRITE_o_WRITE = prove
 (`!c:(S,V)component x y. weakly_valid_component c ==>
   write c x o write c y = write c x`,
  IMP_REWRITE_TAC [FUN_EQ_THM; weakly_valid_component; o_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Additional strongly valid component theorems.                             *)
(* ------------------------------------------------------------------------- *)

let STRONGLY_VALID_COMPONENT_UNWAP = prove
 (`!c:(S,A)component.
        strongly_valid_component c <=>
        read_over_write c /\
        write_over_read c /\
        write_over_write c`,
  REWRITE_TAC[strongly_valid_component; read_over_write;
              write_over_read; write_over_write]);;

(* ------------------------------------------------------------------------- *)
(* Additional extensionally valid component theorems.                        *)
(* ------------------------------------------------------------------------- *)

let EXTENSIONALLY_VALID_COMPONENT_UNWAP = prove
 (`!c:(S,A)component.
        extensionally_valid_component c <=>
        weak_read_over_write c /\
        write_over_read c /\
        write_over_write c`,
  REWRITE_TAC[extensionally_valid_component; weak_read_over_write;
              write_over_read; write_over_write]);;

let EXTENSIONALLY_VALID_COMPONENT = prove
 (`!c. extensionally_valid_component c <=>
        (!y s s'. read c (write c y s) = read c (write c y s')) /\
        (!s. write c (read c s) s = s) /\
        (!y z s. write c z (write c y s) = write c z s)`,
  REWRITE_TAC[extensionally_valid_component] THEN
  REWRITE_TAC[GSYM SKOLEM_THM] THEN MESON_TAC[]);;

let EXTENSIONALLY_VALID_IMP_WEAKLY_VALID_COMPONENT = prove
 (`!c:(S,V)component.
        extensionally_valid_component c ==> weakly_valid_component c`,
  SIMP_TAC[extensionally_valid_component; weakly_valid_component]);;

let EXTENSIONALLY_VALID_COMPONENT_COMPOSE = prove
 (`!c d. strongly_valid_component c /\ extensionally_valid_component d
         ==> extensionally_valid_component(c :> d)`,
  REWRITE_TAC[strongly_valid_component;
              valid_component; EXTENSIONALLY_VALID_COMPONENT;
              READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Additional orthogonal component theorems.                                 *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_COMPONENTS_COMPOSE_LEFT = prove
 (`!sc1 sc2 sc sc'.
        orthogonal_components sc1 sc2
        ==> orthogonal_components (sc1 :> sc) (sc2 :> sc')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[valid_component; orthogonal_components] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[WRITE_COMPONENT_COMPOSE; READ_COMPONENT_COMPOSE]);;

let ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT_GEN = prove
 (`!sc0 sc sc'.
        read_over_write sc0 /\ write_over_write sc0 /\
        orthogonal_components sc sc'
        ==> orthogonal_components (sc0 :> sc) (sc0 :> sc')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[read_over_write; write_over_write] THEN
  REWRITE_TAC[orthogonal_components] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[WRITE_COMPONENT_COMPOSE; READ_COMPONENT_COMPOSE] THEN
  ASM_MESON_TAC[]);;

let ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT = prove
 (`!sc0 sc sc'.
        valid_component sc0 /\ orthogonal_components sc sc'
        ==> orthogonal_components (sc0 :> sc) (sc0 :> sc')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[valid_component; orthogonal_components] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[WRITE_COMPONENT_COMPOSE; READ_COMPONENT_COMPOSE]);;

let ORTHOGONAL_COMPONENTS_SUB_LEFT = prove
 (`!sc1 sc2 sc.
        orthogonal_components sc1 sc2
        ==> orthogonal_components (sc1 :> sc) sc2`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM(CONJUNCT1 COMPOSE_ENTIRETY)] THEN
  ASM_SIMP_TAC[ORTHOGONAL_COMPONENTS_COMPOSE_LEFT]);;

let ORTHOGONAL_COMPONENTS_SUB_RIGHT = prove
 (`!sc1 sc2 sc.
        orthogonal_components sc1 sc2
        ==> orthogonal_components sc1 (sc2 :> sc)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(CONJUNCT1 COMPOSE_ENTIRETY)] THEN
  ASM_SIMP_TAC[ORTHOGONAL_COMPONENTS_COMPOSE_LEFT]);;

let ORTHOGONAL_SPECIAL_COMPONENTS = prove
 (`!c1 c2. write_over_read c1 /\ write_over_read c2 /\
           weak_read_over_write c1 /\ weak_read_over_write c2
           ==> (orthogonal_components c1 c2 <=>
               !y z s. write c1 y (write c2 z s) = write c2 z (write c1 y s))`,
  REWRITE_TAC[write_over_write; write_over_read; weak_read_over_write;
              orthogonal_components] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM METIS_TAC[]);;

let ORTHOGONAL_COMPONENTS = prove
 (`!c1 c2.
        strongly_valid_component c1 /\ strongly_valid_component c2
        ==> (orthogonal_components c1 c2 <=>
             !y z s. write c1 y (write c2 z s) = write c2 z (write c1 y s))`,
  REWRITE_TAC[orthogonal_components; strongly_valid_component; FUN_EQ_THM] THEN
  MESON_TAC[]);;

let ORTHOGONAL_WEAK_COMPONENTS = prove
 (`!c1 c2.
        extensionally_valid_component c1 /\ extensionally_valid_component c2
        ==> (orthogonal_components c1 c2 <=>
             !y z s. write c1 y (write c2 z s) = write c2 z (write c1 y s))`,
  let lemma = prove
   (`!c1 c2.
        extensionally_valid_component c1 /\ extensionally_valid_component c2 /\
        (!y z s. write c1 y (write c2 z s) = write c2 z (write c1 y s))
        ==> (!y s. read c2 (write c1 y s) = read c2 s)`,
    REWRITE_TAC[extensionally_valid_component] THEN STRIP_TAC THEN
    ASM_METIS_TAC[]) in
  REPEAT STRIP_TAC THEN REWRITE_TAC[orthogonal_components] THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN CONJ_TAC THEN
  MATCH_MP_TAC lemma THEN ASM_MESON_TAC[]);;

let READ_WRITE_ORTHOGONAL_COMPONENTS = prove
 (`!c d x s. orthogonal_components c d ==> read c (write d x s) = read c s`,
  REWRITE_TAC[orthogonal_components] THEN MESON_TAC[]);;

let WRITE_SYM = prove
 (`!c:(S,V)component d:(S,V)component f g. orthogonal_components c d ==>
   write c x o write d y = write d y o write c x`,
  REWRITE_TAC [o_DEF; orthogonal_components] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

(* ------------------------------------------------------------------------- *)
(* Pseudo-components for reading only (writing them has no effect).          *)
(* ------------------------------------------------------------------------- *)

let evaluate = define
 `evaluate (f:A->B) = component(f,(\(y:B) (x:A). x))`;;

let READ_WRITE_EVALUATE = prove
 (`(!f:A->B. read (evaluate f) s = f s) /\
   (!(f:A->B) y. write (evaluate f) y s = s)`,
  REWRITE_TAC[read; write; evaluate]);;

let rvalue = define
 `rvalue c = component((\s. c),(\d s. s))`;;

let READ_RVALUE = prove
 (`read(rvalue (c:V)) (s:S) = c`,
  REWRITE_TAC[read; rvalue]);;

let WRITE_RVALUE = prove
 (`write (rvalue c) y s = s`,
  REWRITE_TAC[write; rvalue]);;

let READ_WRITE_RVALUE = prove
 (`(read (rvalue c) = \s. c) /\ (write(rvalue c) = \y s. s)`,
  REWRITE_TAC[FUN_EQ_THM; read; write; rvalue]);;

let COMPONENT_COMPOSE_RVALUE = prove
 (`!y (c:(A,B)component).
        rvalue y :> c = rvalue(read c y)`,
  REWRITE_TAC[COMPONENT_EQ; READ_WRITE_RVALUE; FUN_EQ_THM;
              READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE]);;

let COMPONENT_LCOMPOSE_RVALUE = prove
 (`!(y:V) (c:(A,B)component). extensionally_valid_component c ==>
   c :> rvalue y = rvalue y`,
  REWRITE_TAC[EXTENSIONALLY_VALID_COMPONENT] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[COMPONENT_EQ; READ_WRITE_RVALUE; FUN_EQ_THM;
              READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE]);;

let ORTHOGONAL_COMPONENTS_RVALUE = prove
 (`(!(c:(S,A)component) y. orthogonal_components c (rvalue y)) /\
   (!(c:(S,A)component) y. orthogonal_components (rvalue y) c) /\
   (!(c:(S,A)component) y (d:(A,B)component).
        orthogonal_components c (rvalue y :> d)) /\
   (!(c:(S,A)component) y (d:(A,B)component).
        orthogonal_components (rvalue y :> d) c)`,
  REWRITE_TAC[COMPONENT_COMPOSE_RVALUE] THEN
  REWRITE_TAC[orthogonal_components; READ_WRITE_RVALUE]);;

(* ------------------------------------------------------------------------- *)
(* Apply a pair of (usually mutually inverse) functions (f,g) to component.  *)
(* ------------------------------------------------------------------------- *)

let through = define `through(f,g) = component(f,(\x s. g x))`;;

let READ_WRITE_THROUGH = prove
 (`!f g s. read (through(f,g)) (write (through(f,g)) y s) = f(g y)`,
  REWRITE_TAC[read; through; write]);;

(* ------------------------------------------------------------------------- *)
(* Treat a word component as a numeric component and vice versa.             *)
(* ------------------------------------------------------------------------- *)

let asnumber = define
  `asnumber = through(val:(N)word->num,word:num->(N)word)`;;

let asword = define
  `asword = through(word:num->(N)word,val:(N)word->num)`;;

let READ_WRITE_ASWORD = prove
 (`!y s. read asword (write asword y s) = y`,
  REWRITE_TAC[asword; READ_WRITE_THROUGH; WORD_VAL]);;

let WRITE_ASWORD_MOD = prove
 (`!y:(N)word s n.
     2 EXP dimindex(:N) = n ==> (write asword y s) MOD n = write asword y s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[write; asword; through; write] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[VAL_MOD_REFL]);;

let READ_WRITE_ASNUMBER = prove
 (`!y s:(N)word. read asnumber (write asnumber y s) =
                 y MOD (2 EXP (dimindex(:N)))`,
  REWRITE_TAC[asnumber; READ_WRITE_THROUGH; VAL_WORD]);;

let EXTENSIONALLY_VALID_COMPONENT_ASNUMBER = prove
 (`extensionally_valid_component asnumber`,
  REWRITE_TAC[extensionally_valid_component;
             asnumber; read; write; through] THEN
  REWRITE_TAC[WORD_VAL] THEN
  MATCH_MP_TAC(MESON[] `(?n. P(\x. x MOD n)) ==> ?f. P f`) THEN
  REWRITE_TAC[] THEN MESON_TAC[VAL_WORD]);;

add_extensionally_valid_component_thms
  [EXTENSIONALLY_VALID_COMPONENT_ASNUMBER];;

let WEAKLY_VALID_COMPONENT_ASNUMBER = prove
 (`weakly_valid_component asnumber`,
  REWRITE_TAC[weakly_valid_component; asnumber; read; write; through] THEN
  REWRITE_TAC[WORD_VAL] THEN
  MATCH_MP_TAC(MESON[] `(?n. P(\x. x MOD n)) ==> ?f. P f`) THEN
  REWRITE_TAC[] THEN MESON_TAC[VAL_WORD]);;

add_weakly_valid_component_thms
 [WEAKLY_VALID_COMPONENT_ASNUMBER];;

let VALID_COMPONENT_ASWORD = prove
 (`valid_component(asword:(num,N word)component)`,
  REWRITE_TAC[valid_component; READ_WRITE_ASWORD] THEN
  REWRITE_TAC[asword; read; write; through]);;

add_component_read_write_thms [READ_WRITE_ASNUMBER];;

add_valid_component_thms [VALID_COMPONENT_ASWORD];;

let WEAKLY_VALID_COMPONENT_ASWORD = prove
 (`weakly_valid_component(asword:(num,N word)component)`,
  SIMP_TAC[VALID_IMP_WEAKLY_VALID_COMPONENT; VALID_COMPONENT_ASWORD]);;

add_weakly_valid_component_thms
 [WEAKLY_VALID_COMPONENT_ASWORD];;

(* ------------------------------------------------------------------------- *)
(* State component corresponding to a function (array, bitfield etc.)        *)
(* ------------------------------------------------------------------------- *)

let element = new_definition
 `element i =
    component((\s:I->V. s i),(\v s:I->V j. if j = i then v else s j))`;;

let STRONGLY_VALID_COMPONENT_ELEMENT = prove
 (`!i. strongly_valid_component(element i)`,
  REWRITE_TAC[FUN_EQ_THM; element; read; write; strongly_valid_component] THEN
  MESON_TAC[]);;

add_strongly_valid_component_thms [STRONGLY_VALID_COMPONENT_ELEMENT];;

let EXTENSIONALLY_VALID_COMPONENT_ELEMENT = prove
 (`!i. extensionally_valid_component(element i)`,
  SIMP_TAC[STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT;
           STRONGLY_VALID_COMPONENT_ELEMENT]);;

add_extensionally_valid_component_thms
  [EXTENSIONALLY_VALID_COMPONENT_ELEMENT];;

let VALID_COMPONENT_ELEMENT = prove
 (`!i. valid_component(element i)`,
  REWRITE_TAC[FUN_EQ_THM; element; read; write; valid_component] THEN
  MESON_TAC[]);;

add_valid_component_thms [SPEC_ALL VALID_COMPONENT_ELEMENT];;

let WEAKLY_VALID_COMPONENT_ELEMENT = prove
 (`!i. weakly_valid_component(element i)`,
  SIMP_TAC[VALID_IMP_WEAKLY_VALID_COMPONENT;
           VALID_COMPONENT_ELEMENT]);;

add_weakly_valid_component_thms
  [WEAKLY_VALID_COMPONENT_ELEMENT];;

let READ_ELEMENT = prove
 (`!s i. read (element i) s = s i`,
  REWRITE_TAC[read; element]);;

let READ_WRITE_ELEMENT = prove
 (`!i j y s.
        read (element i) (write (element j) y s) =
        if i = j then y else read (element i) s`,
  REWRITE_TAC[FORALL_COMPONENT; element; read; write]);;

let ORTHOGONAL_COMPONENTS_ELEMENT = prove
 (`!i j. ~(i = j) ==> orthogonal_components (element i) (element j)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[orthogonal_components; read; write; element] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]);;

let ELEMENT_EXTENSIONALITY = prove
 (`!s t. s = t <=> !i. read (element i) s = read (element i) t`,
  REWRITE_TAC[READ_ELEMENT; FUN_EQ_THM]);;

let READ_WRITE_SAME_ELEMENT = prove
 (`!y s. read (element i) (write (element i) y s) = y`,
  REWRITE_TAC[READ_WRITE_ELEMENT]);;

add_component_read_write_thms [READ_WRITE_SAME_ELEMENT];;

(* ------------------------------------------------------------------------- *)
(* Treating a bit within a word as an element.                               *)
(* ------------------------------------------------------------------------- *)

let bitelement = new_definition
 `bitelement i =
    component((\x:N word. bit i x),
              (\b (x:N word).
                  if b then word_of_bits(i INSERT bits_of_word x):N word
                  else word_of_bits(bits_of_word x DELETE i)))`;;

let READ_BITELEMENT = prove
 (`!i. read (bitelement i) = bit i`,
  REWRITE_TAC[FUN_EQ_THM; bitelement; read]);;

let READ_WRITE_BITELEMENT_GEN = prove
 (`!i j y s.
        read (bitelement i) (write (bitelement j) y (s:N word)) =
        if i = j /\ j < dimindex(:N) then y else read (bitelement i) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bitelement; read; write] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BIT_WORD_OF_BITS] THEN
  REWRITE_TAC[IN_INSERT; IN_DELETE; IN_BITS_OF_WORD] THEN
  ASM_MESON_TAC[BIT_TRIVIAL; NOT_LT]);;

let WRITE_WRITE_BITELEMENT = prove
 (`!i j x y (s:N word).
        write (bitelement i) x (write (bitelement i) y s) =
        write (bitelement i) x s`,
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[GSYM READ_BITELEMENT; READ_WRITE_BITELEMENT_GEN] THEN
  MESON_TAC[]);;

let STRONGLY_VALID_COMPONENT_BITELEMENT = prove
 (`!i. i < dimindex(:N)
       ==> strongly_valid_component (bitelement i :(N word,bool)component)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[strongly_valid_component; bitelement; read; write] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OF_BITS; IN_INSERT; IN_DELETE;
                  IN_BITS_OF_WORD] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[BIT_WORD_OF_BITS; IN_INSERT; IN_DELETE] THEN
  REWRITE_TAC[IN_BITS_OF_WORD] THEN ASM_MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let VALID_COMPONENT_BITELEMENT = prove
 (`!i. i < dimindex(:N)
       ==> valid_component (bitelement i :(N word,bool)component)`,
  SIMP_TAC[STRONGLY_VALID_IMP_VALID_COMPONENT;
           STRONGLY_VALID_COMPONENT_BITELEMENT]);;

let EXTENSIONALLY_VALID_COMPONENT_BITELEMENT = prove
 (`!i. i < dimindex(:N)
       ==> extensionally_valid_component
             (bitelement i :(N word,bool)component)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT THEN
  ASM_SIMP_TAC[STRONGLY_VALID_COMPONENT_BITELEMENT]);;

let WEAKLY_VALID_COMPONENT_BITELEMENT = prove
 (`!i. i < dimindex(:N)
       ==> weakly_valid_component
             (bitelement i :(N word,bool)component)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC VALID_IMP_WEAKLY_VALID_COMPONENT THEN
  ASM_SIMP_TAC[VALID_COMPONENT_BITELEMENT]);;

let READ_WRITE_BITELEMENT = prove
 (`!i. i < dimindex(:N)
       ==> !y (s:N word). read (bitelement i) (write (bitelement i) y s) = y`,
  MESON_TAC[REWRITE_RULE[valid_component] VALID_COMPONENT_BITELEMENT]);;

let ORTHOGONAL_COMPONENTS_BITELEMENT = prove
(`!i j. ~(i = j)
        ==> orthogonal_components
             (bitelement i :(N word,bool)component)
             (bitelement j :(N word,bool)component)`,
  SIMP_TAC[orthogonal_components; READ_WRITE_BITELEMENT_GEN] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; GSYM READ_BITELEMENT] THEN
  SIMP_TAC[READ_WRITE_BITELEMENT_GEN] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* State components for subwords of a word.                                  *)
(* The "half" variants exploit the typing to force the correspondence.       *)
(* ------------------------------------------------------------------------- *)

let subword = define
 `subword (pos,len) =
    component
      ((\w. word (((val w) DIV (2 EXP pos)) MOD (2 EXP len))):(N)word->(M)word,
       (\v w. word (2 EXP (pos + len) * (val w DIV (2 EXP (pos + len))) +
              2 EXP pos * (val v) MOD (2 EXP len) +
              (val w) MOD (2 EXP pos))):(M)word->(N)word->(N)word)`;;

let bottomhalf = define
 `bottomhalf:((N tybit0)word,N word)component =
        subword (0,dimindex(:N))`;;

let tophalf = define
 `tophalf:((N tybit0)word,N word)component =
        subword (dimindex(:N),dimindex(:N))`;;

let bottom_256 = define
 `bottom_256:(512 word,256 word)component =
     bottomhalf`;;

let top_256 = define
 `top_256:(512 word,256 word)component = tophalf`;;

let bottom_128 = define
 `bottom_128:(256 word,128 word)component =
     bottomhalf`;;

let top_128 = define
 `top_128:(256 word,128 word)component = tophalf`;;

let bottom_64 = define
 `bottom_64:(128 word,64 word)component = bottomhalf`;;

let top_64 = define
 `top_64:(128 word,64 word)component = tophalf`;;

let bottom_32 = define
 `bottom_32:(64 word,32 word)component = bottomhalf`;;

let top_32 = define
 `top_32:(64 word,32 word)component = tophalf`;;

let bottom_16 = define
 `bottom_16:(32 word,16 word)component = bottomhalf`;;

let top_16 = define
 `top_16:(32 word,16 word)component = tophalf`;;

let bottom_8 = define
 `bottom_8:(16 word,8 word)component = bottomhalf`;;

let top_8 = define
 `top_8:(16 word,8 word)component = tophalf`;;

let READ_SUBWORD = prove
 (`!(w:N word) pos len. read (subword(pos,len)) w = word_subword w (pos,len)`,
  REWRITE_TAC[word_subword; subword; read]);;

let READ_BOTTOM_128 = prove
  (`!s:A. read (c :> bottom_128) s = word_subword (read c s) (0, 128)`,
   REWRITE_TAC[READ_COMPONENT_COMPOSE; bottom_128; bottomhalf;
               DIMINDEX_128; READ_SUBWORD; through; read]);;

let STRONGLY_VALID_COMPONENT_SUBWORD = prove
 (`!pos len.
     dimindex(:M) = len /\ pos + len <= dimindex(:N)
     ==> strongly_valid_component(subword(pos,len):(N word,M word)component)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[strongly_valid_component; subword; read; write] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:(M)word`; `s:(N)word`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM WORD_VAL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[VAL_WORD] THEN
    SIMP_TAC[DIV_MOD; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    SIMP_TAC[GSYM EXP_ADD; MOD_MOD_EXP_MIN; EXP_EQ_0; ARITH_EQ] THEN
    ASM_SIMP_TAC[ARITH_RULE `b <= a ==> MIN a b = b`] THEN
    REWRITE_TAC[MOD_MULT_ADD] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) MOD_LT o lhand o lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[EXP_ADD] THEN MATCH_MP_TAC(ARITH_RULE
       `s < p /\ p * (x + 1) <= p * l ==> p * x + s < p * l`) THEN
      SIMP_TAC[DIVISION; EXP_EQ_0; ARITH; LE_MULT_LCANCEL] THEN
      MATCH_MP_TAC(ARITH_RULE `x < y ==> x + 1 <= y`) THEN
      SIMP_TAC[DIVISION; EXP_EQ_0; ARITH_EQ];
      DISCH_THEN SUBST1_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
      SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
      SIMP_TAC[DIV_LT; DIVISION; EXP_EQ_0; ARITH_EQ; ADD_CLAUSES] THEN
      MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC LTE_TRANS THEN
      EXISTS_TAC `2 EXP (dimindex(:M))` THEN REWRITE_TAC[VAL_BOUND] THEN
      ASM_REWRITE_TAC[LE_REFL; LE_EXP; ARITH_EQ]];
    X_GEN_TAC `s:(N)word` THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM WORD_VAL] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
    `val(s:(N)word) DIV (2 EXP pos) * 2 EXP pos + (val s) MOD (2 EXP pos)` THEN
    CONJ_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC[DIVISION_SIMP; EXP_EQ_0; ARITH_EQ]] THEN
    REWRITE_TAC[ADD_ASSOC; EXP_ADD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(NUM_RING
     `s * l + y:num = z ==> (p * l) * s + p * y = z * p`) THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
    `((val(s:(N)word) DIV (2 EXP pos)) DIV (2 EXP len)) * 2 EXP len +
     (val(s:(N)word) DIV (2 EXP pos)) MOD (2 EXP len)` THEN
    CONJ_TAC THENL
     [ALL_TAC;  ASM_SIMP_TAC[DIVISION_SIMP; EXP_EQ_0; ARITH_EQ]] THEN
    SIMP_TAC[DIV_DIV; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN AP_TERM_TAC THEN
    SIMP_TAC[VAL_WORD; MOD_MOD_EXP_MIN; EXP_EQ_0; ARITH_EQ] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:(M)word`; `y:(M)word`; `s:(N)word`] THEN
    AP_TERM_TAC THEN BINOP_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[VAL_WORD] THEN
      W(MP_TAC o PART_MATCH (lhs o rand) MOD_LT o lhand o lhand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[EXP_ADD] THEN MATCH_MP_TAC(ARITH_RULE
         `z < p /\ p * (l * x + t + 1) <= k
          ==> (p * l) * x + p * t + z < k`) THEN
        SIMP_TAC[DIVISION; EXP_EQ_0; ARITH_EQ] THEN
        FIRST_ASSUM(X_CHOOSE_THEN `d:num` ASSUME_TAC o
          GEN_REWRITE_RULE I [LE_EXISTS]) THEN
        ASM_REWRITE_TAC[EXP_ADD; GSYM MULT_ASSOC] THEN
        REWRITE_TAC[LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
        MATCH_MP_TAC(ARITH_RULE
         `s < p /\ p * (x + 1) <= p * l ==> p * x + s + 1 <= p * l`) THEN
        SIMP_TAC[DIVISION; EXP_EQ_0; ARITH; LE_MULT_LCANCEL] THEN
        MATCH_MP_TAC(ARITH_RULE `x < y ==> x + 1 <= y`) THEN
        SIMP_TAC[GSYM NOT_LE; LE_RDIV_EQ; EXP_EQ_0; ARITH_EQ; MULT_EQ_0] THEN
        REWRITE_TAC[NOT_LE; GSYM EXP_ADD] THEN ASM_MESON_TAC[VAL_BOUND];
        DISCH_THEN SUBST1_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
        SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
        REWRITE_TAC[EQ_ADD_LCANCEL_0] THEN MATCH_MP_TAC DIV_LT THEN
        REWRITE_TAC[EXP_ADD] THEN MATCH_MP_TAC(ARITH_RULE
         `s < p /\ p * (x + 1) <= p * l ==> x * p + s < p * l`) THEN
        SIMP_TAC[DIVISION; EXP_EQ_0; ARITH; LE_MULT_LCANCEL] THEN
        MATCH_MP_TAC(ARITH_RULE `x < y ==> x + 1 <= y`) THEN
        SIMP_TAC[DIVISION; EXP_EQ_0; ARITH_EQ]];
      AP_TERM_TAC THEN REWRITE_TAC[VAL_WORD] THEN
      SIMP_TAC[MOD_MOD_EXP_MIN; ARITH_EQ] THEN
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
       `pos + len <= n ==> MIN n pos = pos`)) THEN
      REWRITE_TAC[EXP_ADD; ARITH_RULE
       `(p * l) * x + p * y + z:num = (l * x + y) * p + z`] THEN
      SIMP_TAC[MOD_MULT_ADD; EXP_EQ_0; ARITH_EQ; MOD_MOD_REFL]]]);;

let VALID_COMPONENT_SUBWORD = prove
 (`!pos len.
     dimindex(:M) = len /\ pos + len <= dimindex(:N)
     ==> valid_component(subword(pos,len):(N word,M word)component)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC STRONGLY_VALID_IMP_VALID_COMPONENT THEN
  MATCH_MP_TAC STRONGLY_VALID_COMPONENT_SUBWORD THEN
  ASM_REWRITE_TAC[]);;

let WRITE_SUBWORD_BITWISE = prove
 (`!pos len (x:(M)word) (s:(N)word).
        bit i (write (subword(pos,len)) x s) =
        if pos <= i /\ i < pos + len /\ i < dimindex(:N) then bit (i - pos) x
        else bit i s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[subword; write] THEN
  DISJ_CASES_TAC(ARITH_RULE `dimindex(:N) <= i \/ i < dimindex(:N)`) THENL
   [ASM_SIMP_TAC[BIT_TRIVIAL; GSYM NOT_LE];
    ASM_REWRITE_TAC[REWRITE_RULE[ODD_MOD] BIT_VAL]] THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (ARITH_RULE `i:num < pos \/ pos <= i /\ i < pos + len \/ pos + len <= i`)
  THENL
   [ASM_REWRITE_TAC[GSYM NOT_LT; VAL_WORD] THEN
    SIMP_TAC[DIV_MOD; MULT_EQ_0; EXP_EQ_0; ARITH_EQ; MOD_MOD_EXP_MIN;
             GSYM(ONCE_REWRITE_RULE[MULT_SYM] (CONJUNCT2 EXP))] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < n ==> MIN n (SUC i) = SUC i`] THEN
    REPLICATE_TAC 2 (AP_THM_TAC THEN AP_TERM_TAC) THEN
    SIMP_TAC[GSYM CONG; ARITH_EQ; EXP_EQ_0; EXP_ADD] THEN
    MATCH_MP_TAC(NUMBER_RULE
     `(n:num) divides p /\ (z == s) (mod n)
      ==> ((p * l) * x + p * y + z == s) (mod n)`) THEN
    ASM_SIMP_TAC[DIVIDES_EXP_LE; ARITH; LE_SUC_LT] THEN
    MATCH_MP_TAC(NUMBER_RULE
     `!m n:num. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)`) THEN
    EXISTS_TAC `2 EXP pos` THEN
    ASM_SIMP_TAC[DIVIDES_EXP_LE; ARITH; CONG_MOD; LE_SUC_LT; EXP_EQ_0];
    ASM_REWRITE_TAC[VAL_WORD] THEN
    SIMP_TAC[DIV_MOD; MULT_EQ_0; EXP_EQ_0; ARITH_EQ; MOD_MOD_EXP_MIN;
             GSYM(ONCE_REWRITE_RULE[MULT_SYM] (CONJUNCT2 EXP))] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < n ==> MIN n (SUC i) = SUC i`] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     `((2 EXP pos * val(x:(M)word) MOD 2 EXP len +
        val(s:(N)word) MOD 2 EXP pos) MOD 2 EXP SUC i)
      DIV (2 EXP i)` THEN
    CONJ_TAC THENL
     [AP_THM_TAC THEN AP_TERM_TAC THEN
      SIMP_TAC[GSYM CONG; ARITH_EQ; EXP_EQ_0] THEN
      MATCH_MP_TAC(NUMBER_RULE
       `(n:num) divides x ==> (x + y == y) (mod n)`) THEN
      MATCH_MP_TAC DIVIDES_RMUL THEN
      SIMP_TAC[DIVIDES_EXP_LE; ARITH] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[ONCE_REWRITE_RULE[MULT_SYM] (CONJUNCT2 EXP);
                 GSYM DIV_MOD; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN `i:num = pos + (i - pos)` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    SIMP_TAC[GSYM DIV_DIV; EXP_ADD; MULT_EQ_0; EXP_EQ_0; ARITH] THEN
    SIMP_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    SIMP_TAC[DIV_LT; DIVISION; EXP_EQ_0; ARITH_EQ; ADD_CLAUSES] THEN
    SIMP_TAC[DIV_MOD; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] (GSYM(CONJUNCT2 EXP))] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[MOD_MOD_EXP_MIN; ARITH_EQ] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    COND_CASES_TAC THENL
     [MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[VAL_WORD] THEN
    SIMP_TAC[DIV_MOD; MULT_EQ_0; EXP_EQ_0; ARITH_EQ; MOD_MOD_EXP_MIN;
             GSYM(ONCE_REWRITE_RULE[MULT_SYM] (CONJUNCT2 EXP))] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < n ==> MIN n (SUC i) = SUC i`] THEN
    ASM_SIMP_TAC[ONCE_REWRITE_RULE[MULT_SYM] (CONJUNCT2 EXP);
                 GSYM DIV_MOD; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    REPLICATE_TAC 2 (AP_THM_TAC THEN AP_TERM_TAC) THEN
    SUBGOAL_THEN `pos + len:num <= i` MP_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC `d:num` THEN DISCH_THEN SUBST_ALL_TAC THEN
    GEN_REWRITE_TAC (PAT_CONV `\x. a DIV x = b DIV x`) [EXP_ADD] THEN
    SIMP_TAC[GSYM DIV_DIV; MULT_EQ_0; EXP_EQ_0; ARITH] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT_ADD; EXP_EQ_0; ARITH] THEN
    REWRITE_TAC[EQ_ADD_LCANCEL_0] THEN SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH] THEN
    REWRITE_TAC[EXP_ADD] THEN MATCH_MP_TAC(ARITH_RULE
     `s < p /\ p * (x + 1) <= p * l ==> p * x + s < p * l`) THEN
    SIMP_TAC[DIVISION; EXP_EQ_0; ARITH; LE_MULT_LCANCEL] THEN
    MATCH_MP_TAC(ARITH_RULE `x < y ==> x + 1 <= y`) THEN
    SIMP_TAC[DIVISION; EXP_EQ_0; ARITH_EQ]]);;

let WRITE_BOTTOM_128 = prove
  (`!s:A y. write (c :> bottom_128) y s =
    write c ((word_join:(128)word->(128)word->(256)word)
      ((word_subword:(256)word->num#num->(128)word)
          (read c s) (128,128)) y) s`,
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[WRITE_COMPONENT_COMPOSE; bottom_128; bottomhalf;
                DIMINDEX_128; through; write] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SPEC_TAC (`read (c:(A,(256)word)component) s:256 word`,`d:256 word`) THEN
    STRIP_TAC THEN
    ONCE_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
    REWRITE_TAC[WRITE_SUBWORD_BITWISE; BIT_WORD_JOIN; BIT_WORD_SUBWORD;
      DIMINDEX_128; DIMINDEX_256] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let READ_WRITE_SUBWORD = prove
 (`!y:(M)word s:(N)word pos len.
      dimindex(:M) <= len /\ pos + len <= dimindex(:N)
      ==> read (subword(pos,len)) (write (subword(pos,len)) y s) = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[subword; read; write] THEN
  REWRITE_TAC[VAL_WORD] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM WORD_VAL] THEN AP_TERM_TAC THEN
  SIMP_TAC[DIV_MOD; EXP_EQ_0; MULT_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[GSYM EXP_ADD] THEN
  SUBGOAL_THEN
    `?d. 2 EXP (dimindex(:N)) = 2 EXP (pos + len) * 2 EXP d`
    (CHOOSE_THEN SUBST1_TAC)
  THENL [ASM_MESON_TAC[LE_EXISTS; EXP_ADD]; ALL_TAC] THEN
  SIMP_TAC[MOD_MOD; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[EXP_ADD] THEN
  SIMP_TAC[GSYM DIV_MOD; EXP_EQ_0; MULT_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[EXP_ADD; ARITH_RULE
   `(p * l) * a + p * b + c:num = (a * l + b) * p + c`] THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  SIMP_TAC[DIV_LT; DIVISION; EXP_EQ_0; ARITH_EQ; ADD_CLAUSES] THEN
  SIMP_TAC[MOD_MULT_ADD; EXP_EQ_0; ARITH_EQ; MOD_MOD_REFL] THEN
  MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `2 EXP (dimindex(:M))` THEN REWRITE_TAC[VAL_BOUND; LE_EXP] THEN
  ASM_ARITH_TAC);;

let READ_SUBWORD_0 = prove
 (`!pos len s. read (subword(pos,len)) (word 0) = word 0`,
  REWRITE_TAC[read; subword; VAL_WORD_0; DIV_0; MOD_0]);;

let READ_SUBWORD_TRIVIAL = prove
 (`!s:(N)word pos len.
        dimindex(:N) <= pos ==> read (subword(pos,len)) s = word 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[read; subword] THEN
  AP_TERM_TAC THEN SIMP_TAC[MOD_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[MULT_CLAUSES] THEN
  SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP (dimindex(:N))` THEN
  ASM_SIMP_TAC[VAL_BOUND; LE_EXP; ARITH]);;

let WRITE_SUBWORD_TRIVIAL = prove
 (`!y:(M)word s:(N)word pos len.
        dimindex(:N) <= pos ==> write (subword(pos,len)) y s = s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[write; subword] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC[VAL_WORD; EXP_ADD] THEN
  SUBGOAL_THEN
    `?d. 2 EXP pos = 2 EXP (dimindex(:N)) * 2 EXP d`
    (CHOOSE_THEN SUBST1_TAC)
  THENL [ASM_MESON_TAC[LE_EXISTS; EXP_ADD]; ALL_TAC] THEN
  REWRITE_TAC[EXP_ADD; GSYM MULT_ASSOC] THEN
  REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE
   `p * l * a + p * b + c:num = (a * l + b) * p + c`] THEN
  SIMP_TAC[MOD_MOD; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  MESON_TAC[VAL_BOUND; MOD_LT]);;

let ORTHOGONAL_COMPONENTS_SUBWORD = prove
 (`!pos1 len1 pos2 len2.
      dimindex(:M) = len1 /\ pos1 + len1 <= dimindex(:N) /\
      dimindex(:M) = len2 /\ pos2 + len2 <= dimindex(:N) /\
      (pos1 + len1 <= pos2 \/ pos2 + len2 <= pos1)
      ==> orthogonal_components
          (subword(pos1,len1):(N word,M word)component)
          (subword(pos2,len2):(N word,M word)component)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) ORTHOGONAL_COMPONENTS o snd) THEN
  (ANTS_TAC THENL
    [ASM_MESON_TAC[STRONGLY_VALID_COMPONENT_SUBWORD]; ALL_TAC]) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[WORD_EQ_BITS] THEN
  SIMP_TAC[WRITE_SUBWORD_BITWISE] THEN ASM_ARITH_TAC);;

let READ_WRITE_HIGHER_SUBWORD = prove
 (`!y:(M)word s:(N)word.
        pos + len <= pos'
        ==> read (subword(pos',len')) (write (subword(pos,len)) y s) =
            read (subword(pos',len')) s`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `dimindex(:N) <= pos'` THEN
  ASM_SIMP_TAC[READ_SUBWORD_TRIVIAL] THEN
  REWRITE_TAC[subword; read; write; VAL_WORD] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM VAL_MOD_REFL] THEN
  SUBGOAL_THEN `?d. dimindex(:N) = pos' + d`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LE_EXISTS] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXP_ADD] THEN
  SIMP_TAC[GSYM DIV_MOD; EXP_EQ_0; MULT_EQ_0; ARITH_EQ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `?e. pos':num = (pos + len) + e`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LE_EXISTS] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[EXP_ADD] THEN
  ONCE_REWRITE_TAC[GSYM EXP_ADD] THEN
  SIMP_TAC[GSYM DIV_DIV; EXP_EQ_0; MULT_EQ_0; ARITH_EQ] THEN
  SIMP_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT_ADD;
           EXP_EQ_0; ARITH_EQ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `x + y = x <=> y = 0`] THEN
  SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `2 EXP pos * (2 EXP len - 1) + 2 EXP pos` THEN CONJ_TAC THENL
   [MATCH_MP_TAC LET_ADD2; ALL_TAC] THEN
  ASM_SIMP_TAC[DIVISION; EXP_EQ_0; ARITH_EQ; LE_MULT_LCANCEL; EXP_ADD;
               ARITH_RULE `p * (n - 1) + p = p * (n - 1 + 1)`;
               ARITH_RULE `l - 1 + 1 <= l <=> ~(l = 0)`;
               ARITH_RULE `x <= y - 1 <=> x = 0 /\ y = 0 \/ x < y`]);;

let READ_WRITE_LOWER_SUBWORD = prove
 (`!y:(M)word s:(N)word.
        pos'  + len' <= pos
        ==> read (subword(pos',len')) (write (subword(pos,len)) y s) =
            read (subword(pos',len')) s`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `dimindex(:N) <= pos` THEN
  ASM_SIMP_TAC[WRITE_SUBWORD_TRIVIAL] THEN
  REWRITE_TAC[subword; read; write] THEN
  SIMP_TAC[DIV_MOD; EXP_EQ_0; MULT_EQ_0; ARITH_EQ] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[VAL_WORD; GSYM EXP_ADD] THEN
  SUBGOAL_THEN
    `?d. 2 EXP (dimindex(:N)) = 2 EXP (pos' + len') * 2 EXP d`
    (CHOOSE_THEN SUBST1_TAC)
  THENL
   [REWRITE_TAC[GSYM EXP_ADD; EQ_EXP; ARITH_EQ; GSYM LE_EXISTS] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[MOD_MOD; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[EXP_ADD; ARITH_RULE
   `(p * l) * a + p * b + c:num = (a * l + b) * p + c`] THEN
  SUBGOAL_THEN
    `?d. 2 EXP pos = 2 EXP (pos' + len') * 2 EXP d`
    (CHOOSE_THEN SUBST1_TAC)
  THENL [ASM_MESON_TAC[LE_EXISTS; EXP_ADD]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `a * b * c + d:num = (a * c) * b + d`] THEN
  SUBST1_TAC(MESON[EXP_ADD]
   `2 EXP pos' * 2 EXP len' = 2 EXP (pos' + len')`) THEN
  REWRITE_TAC[MOD_MULT_ADD] THEN
  SIMP_TAC[MOD_MOD; MULT_EQ_0; EXP_EQ_0; ARITH_EQ]);;

let READ_TOPHALF_BOTTOMHALF_EQ = prove
 (`!x y:(N tybit0)word.
        read tophalf x = read tophalf y /\
        read bottomhalf x = read bottomhalf y <=>
        x = y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bottomhalf; tophalf; subword; read; GSYM word_subword] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_TYBIT0; BIT_WORD_SUBWORD] THEN
  SIMP_TAC[ARITH_RULE `MIN n n = n`; ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `i < 2 * n <=> n <= i /\ i - n < n \/ i < n`] THEN
  REWRITE_TAC[FORALL_AND_THM; TAUT
   `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[LE_EXISTS] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MESON_TAC[ADD_SYM; ADD_SUB]);;

let STRONGLY_VALID_COMPONENT_BOTTOMHALF = prove
 (`strongly_valid_component(bottomhalf:((N tybit0)word,N word)component)`,
  REWRITE_TAC[bottomhalf] THEN
  MATCH_MP_TAC STRONGLY_VALID_COMPONENT_SUBWORD THEN
  REWRITE_TAC[DIMINDEX_TYBIT0] THEN ARITH_TAC);;

let STRONGLY_VALID_COMPONENT_TOPHALF = prove
 (`strongly_valid_component(tophalf:((N tybit0)word,N word)component)`,
  REWRITE_TAC[tophalf] THEN
  MATCH_MP_TAC STRONGLY_VALID_COMPONENT_SUBWORD THEN
  REWRITE_TAC[DIMINDEX_TYBIT0] THEN ARITH_TAC);;

let EXTENSIONALLY_VALID_COMPONENT_BOTTOMHALF = prove
 (`extensionally_valid_component(bottomhalf:((N tybit0)word,N word)component)`,
  MATCH_MP_TAC STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT THEN
  REWRITE_TAC[STRONGLY_VALID_COMPONENT_BOTTOMHALF]);;

let EXTENSIONALLY_VALID_COMPONENT_TOPHALF = prove
 (`extensionally_valid_component(tophalf:((N tybit0)word,N word)component)`,
  MATCH_MP_TAC STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT THEN
  REWRITE_TAC[STRONGLY_VALID_COMPONENT_TOPHALF]);;

let VALID_COMPONENT_BOTTOMHALF = prove
 (`valid_component(bottomhalf:((N tybit0)word,N word)component)`,
  REWRITE_TAC[bottomhalf] THEN
  MATCH_MP_TAC VALID_COMPONENT_SUBWORD THEN
  REWRITE_TAC[DIMINDEX_TYBIT0] THEN ARITH_TAC);;

let VALID_COMPONENT_TOPHALF = prove
 (`valid_component(tophalf:((N tybit0)word,N word)component)`,
  REWRITE_TAC[tophalf] THEN
  MATCH_MP_TAC VALID_COMPONENT_SUBWORD THEN
  REWRITE_TAC[DIMINDEX_TYBIT0] THEN ARITH_TAC);;

let WEAKLY_VALID_COMPONENT_BOTTOMHALF = prove
 (`weakly_valid_component(bottomhalf:((N tybit0)word,N word)component)`,
  MATCH_MP_TAC VALID_IMP_WEAKLY_VALID_COMPONENT THEN
  REWRITE_TAC[VALID_COMPONENT_BOTTOMHALF]);;

let WEAKLY_VALID_COMPONENT_TOPHALF = prove
 (`weakly_valid_component(tophalf:((N tybit0)word,N word)component)`,
  MATCH_MP_TAC VALID_IMP_WEAKLY_VALID_COMPONENT THEN
  REWRITE_TAC[VALID_COMPONENT_TOPHALF]);;

let ORTHOGONAL_COMPONENTS_TOPHALF_BOTTOMHALF = prove
 (`orthogonal_components
        (tophalf:((N tybit0)word,N word)component)
        (bottomhalf:((N tybit0)word,N word)component) /\
   orthogonal_components
        (bottomhalf:((N tybit0)word,N word)component)
        (tophalf:((N tybit0)word,N word)component)`,
  CONJ_TAC THEN REWRITE_TAC[tophalf; bottomhalf] THEN
  MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUBWORD THEN
  REWRITE_TAC[DIMINDEX_TYBIT0] THEN ARITH_TAC);;

add_component_orthogonality_thms
  (CONJUNCTS ORTHOGONAL_COMPONENTS_TOPHALF_BOTTOMHALF);;

let READ_WRITE_TOPHALF_BOTTOMHALF = prove
 (`!s (y:(N)word).
        read tophalf (write tophalf y s) = y /\
        read bottomhalf (write tophalf y s) = read bottomhalf s /\
        read tophalf (write bottomhalf y s) = read tophalf s /\
        read bottomhalf (write bottomhalf y s) = y`,
  REWRITE_TAC[tophalf; bottomhalf] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC READ_WRITE_SUBWORD;
    MATCH_MP_TAC READ_WRITE_LOWER_SUBWORD;
    MATCH_MP_TAC READ_WRITE_HIGHER_SUBWORD;
    MATCH_MP_TAC READ_WRITE_SUBWORD] THEN
  REWRITE_TAC[DIMINDEX_TYBIT0] THEN ARITH_TAC);;

add_strongly_valid_component_thms
  [STRONGLY_VALID_COMPONENT_TOPHALF; STRONGLY_VALID_COMPONENT_BOTTOMHALF];;

add_valid_component_thms
  [VALID_COMPONENT_TOPHALF; VALID_COMPONENT_BOTTOMHALF];;

add_extensionally_valid_component_thms
  [EXTENSIONALLY_VALID_COMPONENT_TOPHALF;
   EXTENSIONALLY_VALID_COMPONENT_BOTTOMHALF];;

add_weakly_valid_component_thms
  [WEAKLY_VALID_COMPONENT_TOPHALF;
   WEAKLY_VALID_COMPONENT_BOTTOMHALF];;

let STRONGLY_VALID_COMPONENT_TOPS = prove
 (`strongly_valid_component top_8 /\
   strongly_valid_component top_16 /\
   strongly_valid_component top_32 /\
   strongly_valid_component top_64 /\
   strongly_valid_component top_128 /\
   strongly_valid_component top_256`,
  REWRITE_TAC[top_8; top_16; top_32; top_64; top_128; top_256] THEN
  REWRITE_TAC[STRONGLY_VALID_COMPONENT_TOPHALF]);;

let STRONGLY_VALID_COMPONENT_BOTTOMS = prove
 (`strongly_valid_component bottom_8 /\
   strongly_valid_component bottom_16 /\
   strongly_valid_component bottom_32 /\
   strongly_valid_component bottom_64 /\
   strongly_valid_component bottom_128 /\
   strongly_valid_component bottom_256`,
  REWRITE_TAC[bottom_8; bottom_16; bottom_32;
              bottom_64; bottom_128; bottom_256] THEN
  REWRITE_TAC[STRONGLY_VALID_COMPONENT_BOTTOMHALF]);;

add_strongly_valid_component_thms
 (CONJUNCTS STRONGLY_VALID_COMPONENT_TOPS @
  CONJUNCTS STRONGLY_VALID_COMPONENT_BOTTOMS);;

let EXTENSIONALLY_VALID_COMPONENT_TOPS = prove
 (`extensionally_valid_component top_8 /\
   extensionally_valid_component top_16 /\
   extensionally_valid_component top_32 /\
   extensionally_valid_component top_64 /\
   extensionally_valid_component top_128 /\
   extensionally_valid_component top_256`,
  REWRITE_TAC[top_8; top_16; top_32; top_64; top_128; top_256] THEN
  REWRITE_TAC[EXTENSIONALLY_VALID_COMPONENT_TOPHALF]);;

let EXTENSIONALLY_VALID_COMPONENT_BOTTOMS = prove
 (`extensionally_valid_component bottom_8 /\
   extensionally_valid_component bottom_16 /\
   extensionally_valid_component bottom_32 /\
   extensionally_valid_component bottom_64 /\
   extensionally_valid_component bottom_128 /\
   extensionally_valid_component bottom_256`,
  REWRITE_TAC[bottom_8; bottom_16; bottom_32;
              bottom_64; bottom_128; bottom_256] THEN
  REWRITE_TAC[EXTENSIONALLY_VALID_COMPONENT_BOTTOMHALF]);;

add_extensionally_valid_component_thms
 (CONJUNCTS EXTENSIONALLY_VALID_COMPONENT_TOPS @
  CONJUNCTS EXTENSIONALLY_VALID_COMPONENT_BOTTOMS);;

let WEAKLY_VALID_COMPONENT_TOPS = prove
 (`weakly_valid_component top_8 /\
   weakly_valid_component top_16 /\
   weakly_valid_component top_32 /\
   weakly_valid_component top_64 /\
   weakly_valid_component top_128 /\
   weakly_valid_component top_256`,
  REWRITE_TAC[top_8; top_16; top_32; top_64; top_128; top_256] THEN
  REWRITE_TAC[WEAKLY_VALID_COMPONENT_TOPHALF]);;

let WEAKLY_VALID_COMPONENT_BOTTOMS = prove
 (`weakly_valid_component bottom_8 /\
   weakly_valid_component bottom_16 /\
   weakly_valid_component bottom_32 /\
   weakly_valid_component bottom_64 /\
   weakly_valid_component bottom_128 /\
   weakly_valid_component bottom_256`,
  REWRITE_TAC[bottom_8; bottom_16; bottom_32;
              bottom_64; bottom_128; bottom_256] THEN
  REWRITE_TAC[WEAKLY_VALID_COMPONENT_BOTTOMHALF]);;

add_weakly_valid_component_thms
 (CONJUNCTS WEAKLY_VALID_COMPONENT_TOPS @
  CONJUNCTS WEAKLY_VALID_COMPONENT_BOTTOMS);;

let VALID_COMPONENT_TOPS = prove
 (`valid_component top_8 /\
   valid_component top_16 /\
   valid_component top_32 /\
   valid_component top_64 /\
   valid_component top_128 /\
   valid_component top_256`,
  REWRITE_TAC[top_8; top_16; top_32; top_64; top_128; top_256] THEN
  REWRITE_TAC[VALID_COMPONENT_TOPHALF]);;

let VALID_COMPONENT_BOTTOMS = prove
 (`valid_component bottom_8 /\
   valid_component bottom_16 /\
   valid_component bottom_32 /\
   valid_component bottom_64 /\
   valid_component bottom_128 /\
   valid_component bottom_256`,
  REWRITE_TAC[bottom_8; bottom_16; bottom_32;
              bottom_64; bottom_128; bottom_256] THEN
  REWRITE_TAC[VALID_COMPONENT_BOTTOMHALF]);;

add_valid_component_thms
 (CONJUNCTS VALID_COMPONENT_TOPS @
  CONJUNCTS VALID_COMPONENT_BOTTOMS);;

add_component_read_write_thms
 (map (CONJUNCT1 o GEN_REWRITE_RULE I [valid_component])
      (CONJUNCTS VALID_COMPONENT_TOPS @
       CONJUNCTS VALID_COMPONENT_BOTTOMS));;

let ORTHOGONAL_COMPONENT_TOP_BOTTOM_8 = prove
 (`orthogonal_components top_8 bottom_8 /\
   orthogonal_components bottom_8 top_8`,
  REWRITE_TAC[top_8; bottom_8] THEN
  REWRITE_TAC[ORTHOGONAL_COMPONENTS_TOPHALF_BOTTOMHALF]);;

let ORTHOGONAL_COMPONENT_TOP_BOTTOM_16 = prove
 (`orthogonal_components top_16 bottom_16 /\
   orthogonal_components bottom_16 top_16`,
  REWRITE_TAC[top_16; bottom_16] THEN
  REWRITE_TAC[ORTHOGONAL_COMPONENTS_TOPHALF_BOTTOMHALF]);;

let ORTHOGONAL_COMPONENT_TOP_BOTTOM_32 = prove
 (`orthogonal_components top_32 bottom_32 /\
   orthogonal_components bottom_32 top_32`,
  REWRITE_TAC[top_32; bottom_32] THEN
  REWRITE_TAC[ORTHOGONAL_COMPONENTS_TOPHALF_BOTTOMHALF]);;

let ORTHOGONAL_COMPONENT_TOP_BOTTOM_64 = prove
 (`orthogonal_components top_64 bottom_64 /\
   orthogonal_components bottom_64 top_64`,
  REWRITE_TAC[top_64; bottom_64] THEN
  REWRITE_TAC[ORTHOGONAL_COMPONENTS_TOPHALF_BOTTOMHALF]);;

let ORTHOGONAL_COMPONENT_TOP_BOTTOM_128 = prove
 (`orthogonal_components top_128 bottom_128 /\
   orthogonal_components bottom_128 top_128`,
  REWRITE_TAC[top_128; bottom_128] THEN
  REWRITE_TAC[ORTHOGONAL_COMPONENTS_TOPHALF_BOTTOMHALF]);;

let ORTHOGONAL_COMPONENT_TOP_BOTTOM_256 = prove
 (`orthogonal_components top_256 bottom_256 /\
   orthogonal_components bottom_256 top_256`,
  REWRITE_TAC[top_256; bottom_256] THEN
  REWRITE_TAC[ORTHOGONAL_COMPONENTS_TOPHALF_BOTTOMHALF]);;

add_component_orthogonality_thms
 (CONJUNCTS ORTHOGONAL_COMPONENT_TOP_BOTTOM_8 @
  CONJUNCTS ORTHOGONAL_COMPONENT_TOP_BOTTOM_16 @
  CONJUNCTS ORTHOGONAL_COMPONENT_TOP_BOTTOM_32 @
  CONJUNCTS ORTHOGONAL_COMPONENT_TOP_BOTTOM_64 @
  CONJUNCTS ORTHOGONAL_COMPONENT_TOP_BOTTOM_128 @
  CONJUNCTS ORTHOGONAL_COMPONENT_TOP_BOTTOM_256);;

let READ_WRITE_256 = prove
 (`!s y. read top_256 (write top_256 y s) = y /\
         read bottom_256 (write top_256 y s) = read bottom_256 s /\
         read top_256 (write bottom_256 y s) = read top_256 s /\
         read bottom_256 (write bottom_256 y s) = y`,
  SIMP_TAC[top_256; bottom_256; READ_WRITE_TOPHALF_BOTTOMHALF]);;

let READ_WRITE_128 = prove
 (`!s y. read top_128 (write top_128 y s) = y /\
         read bottom_128 (write top_128 y s) = read bottom_128 s /\
         read top_128 (write bottom_128 y s) = read top_128 s /\
         read bottom_128 (write bottom_128 y s) = y`,
  SIMP_TAC[top_128; bottom_128; READ_WRITE_TOPHALF_BOTTOMHALF]);;

let READ_WRITE_64 = prove
 (`!s y. read top_64 (write top_64 y s) = y /\
         read bottom_64 (write top_64 y s) = read bottom_64 s /\
         read top_64 (write bottom_64 y s) = read top_64 s /\
         read bottom_64 (write bottom_64 y s) = y`,
  SIMP_TAC[top_64; bottom_64; READ_WRITE_TOPHALF_BOTTOMHALF]);;

let READ_WRITE_32 = prove
 (`!s y. read top_32 (write top_32 y s) = y /\
         read bottom_32 (write top_32 y s) = read bottom_32 s /\
         read top_32 (write bottom_32 y s) = read top_32 s /\
         read bottom_32 (write bottom_32 y s) = y`,
  SIMP_TAC[top_32; bottom_32; READ_WRITE_TOPHALF_BOTTOMHALF]);;

let READ_WRITE_16 = prove
 (`!s y. read top_16 (write top_16 y s) = y /\
         read bottom_16 (write top_16 y s) = read bottom_16 s /\
         read top_16 (write bottom_16 y s) = read top_16 s /\
         read bottom_16 (write bottom_16 y s) = y`,
  SIMP_TAC[top_16; bottom_16; READ_WRITE_TOPHALF_BOTTOMHALF]);;

let READ_WRITE_8 = prove
 (`!s y. read top_8 (write top_8 y s) = y /\
         read bottom_8 (write top_8 y s) = read bottom_8 s /\
         read top_8 (write bottom_8 y s) = read top_8 s /\
         read bottom_8 (write bottom_8 y s) = y`,
  SIMP_TAC[top_8; bottom_8; READ_WRITE_TOPHALF_BOTTOMHALF]);;

let READ_SHORT = prove
 (`!(r:(S,int64)component) s.
        read (r :> bottom_32 :> bottom_16) s =
        word(val (read r s) MOD 65536) /\
        read (r :> bottom_32 :> bottom_16 :> bottom_8) s =
        word(val (read r s) MOD 256) /\
        read (r :> bottom_32 :> bottom_16 :> top_8) s =
        word(val (read r s) DIV 256 MOD 256)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM(NUM_EXP_CONV `2 EXP 8`); GSYM(NUM_EXP_CONV `2 EXP 16`)] THEN
  REWRITE_TAC[GSYM word_subword] THEN ONCE_REWRITE_TAC[MESON[EXP; DIV_1]
    `x MOD 2 EXP n = x DIV 2 EXP 0 MOD 2 EXP n`] THEN
  REWRITE_TAC[GSYM word_subword; READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[bottom_32; bottom_16; bottom_8; top_8] THEN
  REWRITE_TAC[bottomhalf; tophalf; READ_SUBWORD] THEN
  ONCE_REWRITE_TAC [WORD_EQ_BITS_ALT] THEN REWRITE_TAC[BIT_WORD_SUBWORD] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  REPEAT CONJ_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV);;

let WRITE_SHORT = prove
 (`!(r:(S,int64)component) w b s.
    write (r :> bottom_32 :> bottom_16) w s =
    write r (word_join (word_subword (read r s) (16,48):48 word) w) s /\
    write (r :> bottom_32 :> bottom_16 :> bottom_8) b s =
    write r (word_join (word_subword (read r s) (8,56):56 word) b) s /\
    write (r :> bottom_32 :> bottom_16 :> top_8) b s =
    write r (word_join (word_subword (read r s) (16,48):48 word)
                 (word_join b (word_subword (read r s) (0,8):byte):int16)) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WRITE_COMPONENT_COMPOSE] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[bottom_8; top_8; bottom_16; bottom_32] THEN
  REWRITE_TAC[tophalf; bottomhalf] THEN
  ONCE_REWRITE_TAC [WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[WRITE_SUBWORD_BITWISE; READ_SUBWORD; BIT_WORD_JOIN;
              BIT_WORD_SUBWORD] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  REPEAT CONJ_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* A slightly different kind of subword corresponding to the way x86-64      *)
(* and aarch64 treat short registers, forcing zero extension on writes.      *)
(* ------------------------------------------------------------------------- *)

let zerotop_32 = new_definition
  `zerotop_32:(int64,int32)component =
      through(word_zx,word_zx)`;;

let READ_ZEROTOP_32 = prove
 (`!s:A. read (c :> zerotop_32) s = word_zx(read c s)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; zerotop_32; through; read]);;

let WRITE_ZEROTOP_32 = prove
 (`!(s:A) y. write (c :> zerotop_32) y s = write c (word_zx y) s`,
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE; zerotop_32; through; write]);;

let VALID_COMPONENT_ZEROTOP_32 = prove
 (`valid_component zerotop_32`,
  REWRITE_TAC[valid_component; read; write; zerotop_32; through] THEN
  GEN_TAC THEN MATCH_MP_TAC WORD_ZX_ZX THEN
  REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

add_valid_component_thms [VALID_COMPONENT_ZEROTOP_32];;

let WEAKLY_VALID_COMPONENT_ZEROTOP_32 = prove
 (`weakly_valid_component(zerotop_32)`,
  MATCH_MP_TAC VALID_IMP_WEAKLY_VALID_COMPONENT THEN
  REWRITE_TAC[VALID_COMPONENT_ZEROTOP_32]);;

add_weakly_valid_component_thms [WEAKLY_VALID_COMPONENT_ZEROTOP_32];;

add_component_read_write_thms
 [CONJUNCT1(GEN_REWRITE_RULE I [valid_component] VALID_COMPONENT_ZEROTOP_32)];;

(* ------------------------------------------------------------------------- *)
(* Analogous version for other sizes. These are used in aarch64 when         *)
(* writing to smaller parts of SIMD registers (Dn, Sn, Hn, Bn).              *)
(* ------------------------------------------------------------------------- *)

let zerotop_64 = new_definition
  `zerotop_64:(int128,int64)component =
      through(word_zx,word_zx)`;;

let READ_ZEROTOP_64 = prove
 (`!s:A. read (c :> zerotop_64) s = word_zx(read c s)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; zerotop_64; through; read]);;

let WRITE_ZEROTOP_64 = prove
 (`!(s:A) y. write (c :> zerotop_64) y s = write c (word_zx y) s`,
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE; zerotop_64; through; write]);;

let VALID_COMPONENT_ZEROTOP_64 = prove
 (`valid_component zerotop_64`,
  REWRITE_TAC[valid_component; read; write; zerotop_64; through] THEN
  GEN_TAC THEN MATCH_MP_TAC WORD_ZX_ZX THEN
  REWRITE_TAC[DIMINDEX_64; DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV);;

add_valid_component_thms [VALID_COMPONENT_ZEROTOP_64];;

let WEAKLY_VALID_COMPONENT_ZEROTOP_64 = prove
  (`weakly_valid_component(zerotop_64)`,
   MATCH_MP_TAC VALID_IMP_WEAKLY_VALID_COMPONENT THEN
   REWRITE_TAC[VALID_COMPONENT_ZEROTOP_64]);;

add_weakly_valid_component_thms [WEAKLY_VALID_COMPONENT_ZEROTOP_64];;

add_component_read_write_thms
 [CONJUNCT1(GEN_REWRITE_RULE I [valid_component] VALID_COMPONENT_ZEROTOP_64)];;

let zerotop_16 = new_definition
  `zerotop_16:(int32,int16)component =
      through(word_zx,word_zx)`;;

let READ_ZEROTOP_16 = prove
 (`!s:A. read (c :> zerotop_16) s = word_zx(read c s)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; zerotop_16; through; read]);;

let WRITE_ZEROTOP_16 = prove
 (`!(s:A) y. write (c :> zerotop_16) y s = write c (word_zx y) s`,
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE; zerotop_16; through; write]);;

let VALID_COMPONENT_ZEROTOP_16 = prove
 (`valid_component zerotop_16`,
  REWRITE_TAC[valid_component; read; write; zerotop_16; through] THEN
  GEN_TAC THEN MATCH_MP_TAC WORD_ZX_ZX THEN
  REWRITE_TAC[DIMINDEX_16; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV);;

add_valid_component_thms [VALID_COMPONENT_ZEROTOP_16];;

let WEAKLY_VALID_COMPONENT_ZEROTOP_16 = prove
  (`weakly_valid_component(zerotop_16)`,
   MATCH_MP_TAC VALID_IMP_WEAKLY_VALID_COMPONENT THEN
   REWRITE_TAC[VALID_COMPONENT_ZEROTOP_16]);;

add_weakly_valid_component_thms [WEAKLY_VALID_COMPONENT_ZEROTOP_16];;

add_component_read_write_thms
 [CONJUNCT1(GEN_REWRITE_RULE I [valid_component] VALID_COMPONENT_ZEROTOP_16)];;

let zerotop_8 = new_definition
  `zerotop_8:(int16,byte)component =
      through(word_zx,word_zx)`;;

let READ_ZEROTOP_8 = prove
 (`!s:A. read (c :> zerotop_8) s = word_zx(read c s)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; zerotop_8; through; read]);;

let WRITE_ZEROTOP_8 = prove
 (`!(s:A) y. write (c :> zerotop_8) y s = write c (word_zx y) s`,
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE; zerotop_8; through; write]);;

let VALID_COMPONENT_ZEROTOP_8 = prove
 (`valid_component zerotop_8`,
  REWRITE_TAC[valid_component; read; write; zerotop_8; through] THEN
  GEN_TAC THEN MATCH_MP_TAC WORD_ZX_ZX THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV);;

add_valid_component_thms [VALID_COMPONENT_ZEROTOP_8];;

let WEAKLY_VALID_COMPONENT_ZEROTOP_8 = prove
  (`weakly_valid_component(zerotop_8)`,
   MATCH_MP_TAC VALID_IMP_WEAKLY_VALID_COMPONENT THEN
   REWRITE_TAC[VALID_COMPONENT_ZEROTOP_8]);;

add_weakly_valid_component_thms [WEAKLY_VALID_COMPONENT_ZEROTOP_8];;

add_component_read_write_thms
 [CONJUNCT1(GEN_REWRITE_RULE I [valid_component] VALID_COMPONENT_ZEROTOP_8)];;

(* ------------------------------------------------------------------------- *)
(* Dually, larger versions that are used to encode the x86 treatment of      *)
(* writes (but WHEN VEX-ENCODED ONLY!) to XMMs within YMMs within ZMMs.      *)
(* ------------------------------------------------------------------------- *)

let zerotop_128 = new_definition
  `zerotop_128:(256 word,128 word)component =
      through(word_zx,word_zx)`;;

let READ_ZEROTOP_128 = prove
 (`!s:A. read (c :> zerotop_128) s = word_zx(read c s)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; zerotop_128; through; read]);;

let WRITE_ZEROTOP_128 = prove
 (`!(s:A) y. write (c :> zerotop_128) y s = write c (word_zx y) s`,
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE; zerotop_128; through; write]);;

let VALID_COMPONENT_ZEROTOP_128 = prove
 (`valid_component zerotop_128`,
  REWRITE_TAC[valid_component; read; write; zerotop_128; through] THEN
  GEN_TAC THEN MATCH_MP_TAC WORD_ZX_ZX THEN
  REWRITE_TAC[DIMINDEX_128; DIMINDEX_256] THEN CONV_TAC NUM_REDUCE_CONV);;

add_valid_component_thms [VALID_COMPONENT_ZEROTOP_128];;

let WEAKLY_VALID_COMPONENT_ZEROTOP_128 = prove
  (`weakly_valid_component(zerotop_128)`,
   MATCH_MP_TAC VALID_IMP_WEAKLY_VALID_COMPONENT THEN
   REWRITE_TAC[VALID_COMPONENT_ZEROTOP_128]);;

add_weakly_valid_component_thms [WEAKLY_VALID_COMPONENT_ZEROTOP_128];;

add_component_read_write_thms
 [CONJUNCT1(GEN_REWRITE_RULE I [valid_component] VALID_COMPONENT_ZEROTOP_128)];;

let zerotop_256 = new_definition
  `zerotop_256:(512 word,256 word)component =
      through(word_zx,word_zx)`;;

let READ_ZEROTOP_256 = prove
 (`!s:A. read (c :> zerotop_256) s = word_zx(read c s)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; zerotop_256; through; read]);;

let WRITE_ZEROTOP_256 = prove
 (`!(s:A) y. write (c :> zerotop_256) y s = write c (word_zx y) s`,
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE; zerotop_256; through; write]);;

let VALID_COMPONENT_ZEROTOP_256 = prove
 (`valid_component zerotop_256`,
  REWRITE_TAC[valid_component; read; write; zerotop_256; through] THEN
  GEN_TAC THEN MATCH_MP_TAC WORD_ZX_ZX THEN
  REWRITE_TAC[DIMINDEX_256; DIMINDEX_512] THEN CONV_TAC NUM_REDUCE_CONV);;

add_valid_component_thms [VALID_COMPONENT_ZEROTOP_256];;

let WEAKLY_VALID_COMPONENT_ZEROTOP_256 = prove
  (`weakly_valid_component(zerotop_256)`,
   MATCH_MP_TAC VALID_IMP_WEAKLY_VALID_COMPONENT THEN
   REWRITE_TAC[VALID_COMPONENT_ZEROTOP_256]);;

add_weakly_valid_component_thms [WEAKLY_VALID_COMPONENT_ZEROTOP_256];;

add_component_read_write_thms
 [CONJUNCT1(GEN_REWRITE_RULE I [valid_component] VALID_COMPONENT_ZEROTOP_256)];;

(* ------------------------------------------------------------------------- *)
(* State component for a multi-byte chunk of memory treated as a number.     *)
(* NB: This is assuming a *little-endian* encoding.                          *)
(* ------------------------------------------------------------------------- *)

let bytes =
  let th = prove
   (`?bytes:(A word)#num->((A word->byte),num)component.
       (!a s. read (bytes(a,0)) s = 0) /\
       (!a k s. read (bytes(a,SUC k)) s =
                read (bytes(a,k)) s +
                2 EXP (8 * k) * val(s(word_add a (word k)):byte)) /\
       (!a s n. write (bytes(a,0)) n s = s) /\
       (!a k s n. write (bytes(a,SUC k)) n s =
                  write (bytes(a,k)) n
                        (write (element (word_add a (word k)))
                               (word(limb 8 n k)) s))`,
    MATCH_MP_TAC(MESON[]
     `(?r w. P(\i. component(r i,w i))) ==> ?c. P c`) THEN
    REWRITE_TAC[read; write; RIGHT_EXISTS_AND_THM] THEN
    REWRITE_TAC[CONJ_ASSOC; LEFT_EXISTS_AND_THM] THEN CONJ_TAC THEN
    W(ACCEPT_TAC o prove_general_recursive_function_exists o snd)) in
  new_specification ["bytes"] th;;

let READ_ELEMENT_WRITE_BYTES = prove
 (`!a (b:A word) k n s.
        read (element b) (write (bytes(a,k)) n s) =
          if val(word_sub b a) < k
          then word(limb 8 n (val(word_sub b a)))
          else read (element b) s`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  SIMP_TAC[bytes; LT] THEN
  X_GEN_TAC `k:num` THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_CASES_TAC `val(word_sub b a:A word) < k` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_GALOIS; READ_WRITE_ELEMENT] THEN
  REWRITE_TAC[WORD_RULE `b:A word = word_add a k <=> word_sub b a = k`] THEN
  ASM_CASES_TAC `word_sub b a:A word = word k` THEN
  ASM_SIMP_TAC[VAL_WORD_EQ] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD; NOT_LT]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
   `k <= k MOD n ==> k MOD n <= k ==> k MOD n = k`)) THEN
  REWRITE_TAC[MOD_LE; MOD_EQ_SELF; EXP_EQ_0] THEN ASM_ARITH_TAC);;

let READ_BYTES = prove
 (`!(a:A word) k s.
        read (bytes(a,k)) s =
        nsum {i | i < k}
             (\i. 2 EXP (8 * i) * val(s(word_add a (word i))))`,
  GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[bytes; NSUM_CLAUSES_NUMSEG_LT] THEN
  X_GEN_TAC `k:num` THEN ASM_CASES_TAC `k < 2 EXP dimindex(:A)` THEN
  ASM_REWRITE_TAC[LE_SUC_LT] THEN ASM_SIMP_TAC[LT_IMP_LE]);;

let EXTENSIONALLY_VALID_COMPONENT_BYTES = prove
 (`!(a:A word) k. extensionally_valid_component(bytes(a,k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[extensionally_valid_component] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC
     `\y. nsum {i | i < k}
               (\i. 2 EXP (8 * i) * limb 8 y (i MOD 2 EXP dimindex(:A)))` THEN
    REWRITE_TAC[READ_BYTES] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[REWRITE_RULE[READ_ELEMENT] READ_ELEMENT_WRITE_BYTES] THEN
    REWRITE_TAC[WORD_RULE `word_sub (word_add a i) a = i`] THEN
    MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[VAL_WORD] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[VAL_WORD; MOD_EQ_SELF; DIMINDEX_8; LIMB_BOUND] THEN
    ASM_MESON_TAC[MOD_LE; LET_TRANS];
    X_GEN_TAC `s:A word->byte` THEN REWRITE_TAC[ELEMENT_EXTENSIONALITY] THEN
    X_GEN_TAC `b:A word` THEN
    REWRITE_TAC[READ_ELEMENT_WRITE_BYTES] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[READ_BYTES] THEN
    SIMP_TAC[LIMB_DIGITSUM; VAL_BOUND; GSYM DIMINDEX_8] THEN
    ASM_REWRITE_TAC[WORD_VAL; READ_ELEMENT] THEN
    AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    SIMP_TAC[ELEMENT_EXTENSIONALITY; READ_ELEMENT_WRITE_BYTES]]);;

add_extensionally_valid_component_thms
 [EXTENSIONALLY_VALID_COMPONENT_BYTES];;

let ORTHOGONAL_COMPONENTS_BYTES = prove
 (`!(a:A word) k b j.
        orthogonal_components (bytes(a,k)) (bytes(b,j)) <=>
        nonoverlapping_modulo (2 EXP dimindex(:A)) (val a,k) (val b,j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nonoverlapping_modulo] THEN
  SIMP_TAC[ORTHOGONAL_WEAK_COMPONENTS; NOT_EXISTS_THM;
           EXTENSIONALLY_VALID_COMPONENT_BYTES] THEN
  REWRITE_TAC[ELEMENT_EXTENSIONALITY; READ_ELEMENT_WRITE_BYTES] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`nsum {i | i < k} (\i. 2 EXP (8 * i) * 1)`; `0`;
      `s:A word->byte`; `word_add a (word m):A word`]) THEN
    REWRITE_TAC[WORD_RULE `word_sub (word_add a x) a = x`] THEN
    SIMP_TAC[LIMB_0; LIMB_DIGITSUM; ARITH_RULE `1 < 2 EXP 8`] THEN
    MATCH_MP_TAC(MESON[]
     `~(a = c) /\ p /\ q
      ==> ~((if p then a else b) = (if q then c else d))`) THEN
    REWRITE_TAC[WORD_NE_10] THEN
    SUBGOAL_THEN `word_add a (word m):A word = word_add b (word n)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD] THEN
      CONV_TAC MOD_DOWN_CONV THEN ASM_REWRITE_TAC[GSYM CONG];
      REWRITE_TAC[WORD_RULE `word_sub (word_add a x) a = x`] THEN
      REWRITE_TAC[VAL_WORD] THEN ASM_MESON_TAC[LET_TRANS; MOD_LE]];
    MAP_EVERY X_GEN_TAC [`y:num`; `z:num`; `s:A word->byte`; `c:A word`] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`val(word_sub c a:A word)`; `val(word_sub c b:A word)`]) THEN
    ASM_REWRITE_TAC[CONG; GSYM VAL_WORD_ADD] THEN
    REWRITE_TAC[WORD_RULE `word_add a (word_sub x a) = x`]]);;

let READ_WRITE_BYTES = prove
 (`!(a:A word) k y s.
           k <= 2 EXP dimindex(:A)
           ==> read (bytes (a,k)) (write (bytes (a,k)) y s) =
               y MOD 2 EXP (8 * k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[READ_BYTES] THEN
  REWRITE_TAC[REWRITE_RULE[READ_ELEMENT] READ_ELEMENT_WRITE_BYTES] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add a i) a = i`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM DIGITSUM_WORDS_LIMB_GEN] THEN
  MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `i < 2 EXP dimindex(:A)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[VAL_WORD; MOD_LT]] THEN
  AP_TERM_TAC THEN ASM_REWRITE_TAC[MOD_EQ_SELF; DIMINDEX_8; LIMB_BOUND]);;

let READ_BYTES_TRIVIAL = prove
 (`!addr. read (bytes(addr,0)) s = 0`,
  REWRITE_TAC[READ_BYTES; NSUM_CLAUSES_NUMSEG_LT]);;

let WEAKLY_VALID_COMPONENT_BYTES = prove
 (`!addr len. weakly_valid_component(bytes(addr,len))`,
  SIMP_TAC[EXTENSIONALLY_VALID_IMP_WEAKLY_VALID_COMPONENT;
           EXTENSIONALLY_VALID_COMPONENT_BYTES]);;

add_weakly_valid_component_thms
 [WEAKLY_VALID_COMPONENT_BYTES];;

let READ_BYTES_BOUND = prove
 (`!pos len s. read (bytes(pos,len)) s < 2 EXP (8 * len)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_BYTES; EXP_MULT] THEN
  MATCH_MP_TAC DIGITSUM_BOUND THEN
  REWRITE_TAC[VAL_BOUND; GSYM DIMINDEX_8]);;

let READ_BYTES_BOUND_ALT = prove
 (`!pos len s. read (bytes (pos,len)) s < 256 EXP len`,
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP] THEN
  REWRITE_TAC[READ_BYTES_BOUND]);;

let READ_BYTES_MOD_LEN = prove
 (`!pos len s. (read (bytes(pos,len)) s) MOD (2 EXP (8 * len)) =
               read (bytes(pos,len)) s`,
  SIMP_TAC[MOD_LT; READ_BYTES_BOUND]);;

let WRITE_BYTES = prove
 (`!(a:A word) k n.
        write (bytes(a,k)) n =
        \s b. if val(word_sub b a) < k
              then word (limb 8 n (val (word_sub b a)))
              else s b`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN GEN_TAC THEN
  GEN_REWRITE_TAC I [ELEMENT_EXTENSIONALITY] THEN
  REWRITE_TAC[READ_ELEMENT_WRITE_BYTES] THEN REWRITE_TAC[READ_ELEMENT]);;

let READ_BYTES_1 = prove
 (`!(a:A word) n. read (bytes(a,1)) s = val (s a)`,
  REWRITE_TAC [ONE; bytes] THEN
  REWRITE_TAC [MULT_CLAUSES; EXP; ADD; WORD_ADD_0]);;

let WRITE_BYTES_1 = prove
 (`!(a:A word) n. write (bytes(a,1)) n = write (element a) (word n)`,
  REWRITE_TAC [FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [ONE; bytes; WORD_ADD_0] THEN
  REWRITE_TAC [limb; MULT_0; EXP; DIV_1;
    CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV)
      (INST_TYPE [`:8`,`:N`] WORD_MOD_SIZE)]);;

let WRITE_BYTES_RESTRICT = prove
 (`!(a:A word) k n.
        write (bytes(a,k)) n =
        write (bytes(a,k)) (n MOD 2 EXP (8 * k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WRITE_BYTES; FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:A word->byte`; `b:A word`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[limb] THEN AP_TERM_TAC THEN
  REWRITE_TAC[DIV_MOD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let READ_BYTES_COMBINE = prove
 (`!(a:A word) m n s.
        read (bytes(a,m+n)) s =
        read (bytes(a,m)) s +
        2 EXP (8 * m) * read (bytes(word_add a (word m),n)) s`,
  GEN_TAC THEN GEN_TAC THEN GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  X_GEN_TAC `s:A word->byte` THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; bytes] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; GSYM ADD_ASSOC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EQ_ADD_LCANCEL] THEN
  REWRITE_TAC[WORD_ADD; EXP_ADD; GSYM MULT_ASSOC] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC]);;

let WRITE_BYTES_COMBINE = prove
 (`!(a:A word) m n x y s.
        write (bytes(a,m+n)) (x MOD 2 EXP (8 * m) + 2 EXP (8 * m) * y) s =
        write (bytes(a,m)) x (write (bytes(word_add a (word m),n)) y s)`,
  REPEAT GEN_TAC THEN SPECL_TAC [`n:num`; `y:num`; `s:A word->byte`] THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; bytes] THENL
   [ONCE_REWRITE_TAC[WRITE_BYTES_RESTRICT] THEN
    REWRITE_TAC[MOD_MULT_ADD; MOD_MOD_REFL];
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; limb;
      DIV_MULT_ADD; EXP_ADD; LEFT_ADD_DISTRIB] THEN
    IMP_REWRITE_TAC [GSYM DIV_DIV; EXP_2_NE_0; DIV_MULT_ADD;
      ADD_CLAUSES; MOD_DIV_EQ_0]]);;

let READ_BYTES_EQ = prove
 (`!s s' a n.
        read (bytes(a,n)) s = read (bytes(a,n)) s' <=>
        !i. i < n ==> s(word_add a (word i)) = s'(word_add a (word i))`,
  GEN_TAC THEN GEN_TAC THEN GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  INDUCT_TAC THEN REWRITE_TAC[bytes] THEN
  ASM_REWRITE_TAC[CONJUNCT1 LT; MESON[LT]
   `(!i. i < SUC n ==> P i) <=> (!i. i < n ==> P i) /\ P n`] THEN
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  MATCH_MP_TAC(TAUT
   `(q ==> (p <=> r)) /\ (p ==> q)  ==> p ==> q /\ r`) THEN
  SIMP_TAC[EQ_ADD_LCANCEL; EQ_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ; VAL_EQ] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP (8 * n)`) THEN
  REWRITE_TAC[MOD_MULT_ADD; READ_BYTES_MOD_LEN]);;

let READ_BYTES_MOD = prove
 (`!(a:N word) k n s.
        read (bytes(a,k)) s MOD (2 EXP (8 * n)) =
        read (bytes(a,MIN k n)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_BYTES; EXP_MULT] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) DIGITSUM_MOD o lhand o snd) THEN
  REWRITE_TAC[IN_ELIM_THM; ARITH_RULE `i < MIN k n <=> i < k /\ i < n`] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[GSYM DIMINDEX_8; VAL_BOUND]);;

let READ_BYTES_DIV = prove
 (`!a k n s. read (bytes(a,k)) s DIV (2 EXP (8 * n)) =
             read (bytes(word_add a (word n),k - n)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_BYTES; EXP_MULT] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) DIGITSUM_DIV_NUMSEG o lhand o snd) THEN
  REWRITE_TAC[GSYM WORD_ADD; ADD_AC; GSYM WORD_ADD_ASSOC] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[GSYM DIMINDEX_8; VAL_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* A state component for byte lists.                                         *)
(* ------------------------------------------------------------------------- *)

let bytelist = define
 `bytelist(a,n) = bytes(a,n) :> through(bytelist_of_num n,num_of_bytelist)`;;

let bytelist_clauses = prove
 (`(!(a:A word) s. read (bytelist (a,0)) s = []) /\
   (!(a:A word) k s.
     read (bytelist (a,SUC k)) s =
     CONS (s a) (read (bytelist (word_add a (word 1),k)) s)) /\
   (!(a:A word) l s. write (bytelist (a,0)) l s = s) /\
   (!(a:A word) k s. write (bytelist (a,SUC k)) [] s =
     write (element a) (word 0)
       (write (bytelist (word_add a (word 1),k)) [] s)) /\
   (!(a:A word) k s n l. write (bytelist (a,SUC k)) (CONS n l) s =
     write (element a) n (write (bytelist (word_add a (word 1),k)) l s))`,
  SUBGOAL_THEN `!(a:A word) k s n l. write (bytelist (a,SUC k)) (CONS n l) s =
     write (element a) n (write (bytelist (word_add a (word 1),k)) l s)`
    (fun th -> REWRITE_TAC [th] THEN REWRITE_TAC [GSYM th]) THEN
  REWRITE_TAC [bytelist; READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE;
    read; write; through; bytelist_of_num; num_of_bytelist; bytes] THEN
  REPEAT STRIP_TAC THENL [
    SPEC1_TAC `n:byte` THEN REWRITE_TAC [FORALL_VAL_GEN] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC [GSYM WRITE_BYTES_1; GSYM WRITE_BYTES_COMBINE; ADD_SYM;
      limb] THEN ONCE_REWRITE_TAC [WRITE_BYTES_RESTRICT] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [EXP_MULT] THEN
    POP_ASSUM (MP_TAC o CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
    SPEC1_TAC `k:num` THEN INDUCT_TAC THEN REWRITE_TAC [GSYM ADD1; EXP;
      EXP_1; MOD_1; DIV_1; ADD_CLAUSES; MULT_CLAUSES; MOD_MULT_ADD] THEN
    ONCE_REWRITE_TAC [GSYM MOD_MULT_MOD] THEN REWRITE_TAC [
      MATCH_MP MOD_LT (ASSUME `n < 256`); MULT_AC; ADD_AC; MOD_MOD_REFL];
    REWRITE_TAC [GSYM bytes; ONCE_REWRITE_RULE [ADD_SYM] ADD1;
      READ_BYTES_COMBINE; READ_BYTES_1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN IMP_REWRITE_TAC [
      DIV_MULT_ADD; ARITH_RULE `~(256 = 0)`; MOD_MULT_ADD; DIV_LT; MOD_LT;
      ADD; WORD_VAL; CONV_RULE
        (ONCE_DEPTH_CONV DIMINDEX_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV)
        (INST_TYPE [`:8`,`:N`] VAL_BOUND)];
    REWRITE_TAC [MULT_0; ADD_0; VAL_WORD_0]]);;

let read_bytelist_append = prove
 (`read (bytelist (pc, LENGTH (APPEND l1 l2))) s = APPEND l1 l2 <=>
   read (bytelist (pc:A word, LENGTH l1)) s = l1 /\
   read (bytelist (word_add pc (word (LENGTH l1)), LENGTH l2)) s = l2`,
  SPECL_TAC [`l1:byte list`; `pc:A word`] THEN LIST_INDUCT_TAC THEN
  GEN_TAC THEN REWRITE_TAC [APPEND; LENGTH; WORD_ADD_0] THEN
  ASM_REWRITE_TAC [bytelist_clauses; CONS_11; CONJ_ACI;
    WORD_RULE `word_add (word_add (pc:A word) (word 1)) (word (LENGTH t)) =
      word_add pc (word (SUC (LENGTH t)))`]);;

let EXTENSIONALLY_VALID_COMPONENT_BYTELIST = prove
 (`!(a:A word) k. extensionally_valid_component(bytelist(a,k))`,
  let th1,th2 = CONJ_PAIR (REWRITE_RULE [extensionally_valid_component]
      (SPEC_ALL EXTENSIONALLY_VALID_COMPONENT_BYTES)) in
  REPEAT GEN_TAC THEN REWRITE_TAC [extensionally_valid_component; bytelist;
    read; write; component_compose; through; o_THM; NUM_OF_BYTELIST_OF_NUM;
    th2; REWRITE_RULE [EXP_MULT; ARITH_RULE `2 EXP 8 = 256`]
      (GSYM WRITE_BYTES_RESTRICT)] THEN
  CHOOSE_THEN (fun f ->
    REWRITE_TAC [f; GSYM SKOLEM_THM] THEN MESON_TAC []) th1);;

add_extensionally_valid_component_thms
 [EXTENSIONALLY_VALID_COMPONENT_BYTELIST];;

(* ------------------------------------------------------------------------- *)
(* Variant of bytes returning a "natural" word. This still needs some        *)
(* range conditions in general so we tend to use specific cases below.       *)
(* ------------------------------------------------------------------------- *)

let wbytes = new_definition
 `wbytes a :((A word->byte),N word)component =
    bytes(a,dimindex(:N) DIV 8) :> asword`;;

let VAL_READ_WBYTES = prove
 (`!(a:A word) s.
        val(read (wbytes a) s:N word) = read (bytes(a,dimindex(:N) DIV 8)) s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wbytes; asword; through; read; READ_COMPONENT_COMPOSE] THEN
  MATCH_MP_TAC VAL_WORD_EQ THEN
  TRANS_TAC LTE_TRANS `2 EXP (8 * dimindex(:N) DIV 8)` THEN
  REWRITE_TAC[READ_BYTES_BOUND; LE_EXP] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Specifically sized versions of "bytes" returning words. The address word  *)
(* type is inferred from the memory component with which these are composed. *)
(* Strong validity additionally requires the view to fit in the address      *)
(* space; concrete 32- and 64-bit address types satisfy every condition here. *)
(* ------------------------------------------------------------------------- *)

let bytes8 = define
 `bytes8 (addr:A word) :((A word->byte),byte)component =
    bytes(addr,1) :> asword`;;

let bytes16 = define
 `bytes16 (addr:A word) :((A word->byte),int16)component =
    bytes(addr,2) :> asword`;;

let bytes32 = define
 `bytes32 (addr:A word) :((A word->byte),int32)component =
    bytes(addr,4) :> asword`;;

let bytes64 = define
 `bytes64 (addr:A word) :((A word->byte),int64)component =
    bytes(addr,8) :> asword`;;

let bytes128 = define
 `bytes128 (addr:A word) :((A word->byte),int128)component =
    bytes(addr,16) :> asword`;;

let bytes256 = define
 `bytes256 (addr:A word) :((A word->byte),256 word)component =
    bytes(addr,32) :> asword`;;

(* Keep unconstrained quotations such as `bytes32` at their historical
   int64 instance. Existing ARM and x86 proof scripts use exact OCaml-level
   term searches for these quotations. A surrounding memory component or an
   explicit address type still selects any other instance of the same
   polymorphic HOL constant.

   For example, in `memory32 :> bytes32 p32`, the component types select
   32-bit addresses. A bare quotation of `bytes32` has no such context and
   keeps the historical int64 instance.

   TODO: This preference is only a compatibility convenience to avoid churn
   in the existing 64-bit models. Remove it once those exact term searches
   recognize the polymorphic constant independently of its instantiation. *)

make_overloadable "bytes8"
 `:A word->((A word->byte),byte)component`;;
overload_interface
 ("bytes8",`bytes8:A word->((A word->byte),byte)component`);;
overload_interface
 ("bytes8",`bytes8:int64->((int64->byte),byte)component`);;

make_overloadable "bytes16"
 `:A word->((A word->byte),int16)component`;;
overload_interface
 ("bytes16",`bytes16:A word->((A word->byte),int16)component`);;
overload_interface
 ("bytes16",`bytes16:int64->((int64->byte),int16)component`);;

make_overloadable "bytes32"
 `:A word->((A word->byte),int32)component`;;
overload_interface
 ("bytes32",`bytes32:A word->((A word->byte),int32)component`);;
overload_interface
 ("bytes32",`bytes32:int64->((int64->byte),int32)component`);;

make_overloadable "bytes64"
 `:A word->((A word->byte),int64)component`;;
overload_interface
 ("bytes64",`bytes64:A word->((A word->byte),int64)component`);;
overload_interface
 ("bytes64",`bytes64:int64->((int64->byte),int64)component`);;

make_overloadable "bytes128"
 `:A word->((A word->byte),int128)component`;;
overload_interface
 ("bytes128",`bytes128:A word->((A word->byte),int128)component`);;
overload_interface
 ("bytes128",`bytes128:int64->((int64->byte),int128)component`);;

make_overloadable "bytes256"
 `:A word->((A word->byte),256 word)component`;;
overload_interface
 ("bytes256",`bytes256:A word->((A word->byte),256 word)component`);;
overload_interface
 ("bytes256",`bytes256:int64->((int64->byte),256 word)component`);;

let BYTES8_ELEMENT = prove
 (`(bytes8:A word->((A word->byte),byte)component) = element`,
  REWRITE_TAC[FUN_EQ_THM; COMPONENT_EQ] THEN
  REWRITE_TAC[bytes8; READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[READ_BYTES_1; WRITE_BYTES_1] THEN
  REWRITE_TAC[asword; write; through; read] THEN
  REWRITE_TAC[GSYM DIMINDEX_8; VAL_MOD_REFL; WORD_VAL; READ_ELEMENT]);;

let READ_BYTES_BYTES8 = prove
 (`!(a:A word) s. read (bytes(a,1)) s = val(read (bytes8 a) s)`,
  REWRITE_TAC[READ_BYTES_1; BYTES8_ELEMENT; READ_ELEMENT]);;

let READ_MEMORY_BYTES_BYTES8 = prove
 (`!m (a:A word) s.
      read (m :> bytes(a,1)) s = val(read (m :> bytes8 a) s)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BYTES8]);;

let READ_ELEMENT_WRITE_BYTES8 = prove
 (`!(a:A word) b w m.
        read (element b) (write (bytes8 a) w m) =
        if b = a then w else read (element b) m`,
  REWRITE_TAC[BYTES8_ELEMENT; READ_WRITE_ELEMENT]);;

let BYTES8_WBYTES = prove
 (`(bytes8:A word->((A word->byte),byte)component) = wbytes`,
  REWRITE_TAC[FUN_EQ_THM; wbytes; bytes8] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let BYTES16_WBYTES = prove
 (`(bytes16:A word->((A word->byte),int16)component) = wbytes`,
  REWRITE_TAC[FUN_EQ_THM; wbytes; bytes16] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let BYTES32_WBYTES = prove
 (`(bytes32:A word->((A word->byte),int32)component) = wbytes`,
  REWRITE_TAC[FUN_EQ_THM; wbytes; bytes32] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let BYTES64_WBYTES = prove
 (`(bytes64:A word->((A word->byte),int64)component) = wbytes`,
  REWRITE_TAC[FUN_EQ_THM; wbytes; bytes64] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let BYTES128_WBYTES = prove
 (`(bytes128:A word->((A word->byte),int128)component) = wbytes`,
  REWRITE_TAC[FUN_EQ_THM; wbytes; bytes128] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let BYTES256_WBYTES = prove
 (`(bytes256:A word->((A word->byte),256 word)component) = wbytes`,
  REWRITE_TAC[FUN_EQ_THM; wbytes; bytes256] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let STRONGLY_VALID_COMPONENT_BYTES8 = prove
 (`!a:A word. strongly_valid_component (bytes8 a)`,
  GEN_TAC THEN
  SUBGOAL_THEN `1 <= 2 EXP dimindex(:A)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM(NUM_REDUCE_CONV `2 EXP 0`)] THEN
    REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:A word`; `1`] EXTENSIONALLY_VALID_COMPONENT_BYTES) THEN
  MP_TAC(ISPECL [`a:A word`; `1`] READ_WRITE_BYTES) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[strongly_valid_component; EXTENSIONALLY_VALID_COMPONENT] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[bytes8; READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[read; write; asword; through; VAL_WORD] THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBST1_TAC(ARITH_RULE `256 = 2 EXP (8 * 1)`) THEN
  ASM_REWRITE_TAC[READ_BYTES_MOD_LEN] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[GSYM DIMINDEX_8; VAL_MOD_REFL; WORD_VAL]);;

let EXTENSIONALLY_VALID_COMPONENT_BYTES8 = prove
 (`!a:A word. extensionally_valid_component (bytes8 a)`,
  SIMP_TAC[STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT;
           STRONGLY_VALID_COMPONENT_BYTES8]);;

let VALID_COMPONENT_BYTES8 = prove
 (`!a:A word. valid_component (bytes8 a)`,
  SIMP_TAC[STRONGLY_VALID_IMP_VALID_COMPONENT;
           STRONGLY_VALID_COMPONENT_BYTES8]);;

let WEAKLY_VALID_COMPONENT_BYTES8 = prove
 (`!a:A word. weakly_valid_component (bytes8 a)`,
  SIMP_TAC[VALID_IMP_WEAKLY_VALID_COMPONENT;
           VALID_COMPONENT_BYTES8]);;

let STRONGLY_VALID_COMPONENT_BYTES16 = prove
 (`!a:A word. strongly_valid_component (bytes16 a)`,
  GEN_TAC THEN
  SUBGOAL_THEN `2 <= 2 EXP dimindex(:A)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM(NUM_REDUCE_CONV `2 EXP 1`)] THEN
    REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
    MP_TAC(ISPEC `UNIV:A->bool` DIMINDEX_GE_1) THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:A word`; `2`] EXTENSIONALLY_VALID_COMPONENT_BYTES) THEN
  MP_TAC(ISPECL [`a:A word`; `2`] READ_WRITE_BYTES) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[strongly_valid_component; EXTENSIONALLY_VALID_COMPONENT] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[bytes16; READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[read; write; asword; through; VAL_WORD] THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBST1_TAC(ARITH_RULE `65536 = 2 EXP (8 * 2)`) THEN
  ASM_REWRITE_TAC[READ_BYTES_MOD_LEN] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[GSYM DIMINDEX_16; VAL_MOD_REFL; WORD_VAL]);;

let EXTENSIONALLY_VALID_COMPONENT_BYTES16 = prove
 (`!a:A word. extensionally_valid_component (bytes16 a)`,
  SIMP_TAC[STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT;
           STRONGLY_VALID_COMPONENT_BYTES16]);;

let VALID_COMPONENT_BYTES16 = prove
 (`!a:A word. valid_component (bytes16 a)`,
  SIMP_TAC[STRONGLY_VALID_IMP_VALID_COMPONENT;
           STRONGLY_VALID_COMPONENT_BYTES16]);;

let WEAKLY_VALID_COMPONENT_BYTES16 = prove
 (`!a:A word. weakly_valid_component (bytes16 a)`,
  SIMP_TAC[VALID_IMP_WEAKLY_VALID_COMPONENT;
           VALID_COMPONENT_BYTES16]);;

let STRONGLY_VALID_COMPONENT_BYTES32 = prove
 (`!a:(N tybit0)word. strongly_valid_component (bytes32 a)`,
  GEN_TAC THEN
  SUBGOAL_THEN `4 <= 2 EXP dimindex(:(N tybit0))` ASSUME_TAC THENL
   [REWRITE_TAC[DIMINDEX_TYBIT0] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM(NUM_REDUCE_CONV `2 EXP 2`)] THEN
    REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
    MP_TAC(ISPEC `UNIV:N->bool` DIMINDEX_GE_1) THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:(N tybit0)word`; `4`]
    EXTENSIONALLY_VALID_COMPONENT_BYTES) THEN
  MP_TAC(ISPECL [`a:(N tybit0)word`; `4`] READ_WRITE_BYTES) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[strongly_valid_component; EXTENSIONALLY_VALID_COMPONENT] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[bytes32; READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[read; write; asword; through; VAL_WORD] THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBST1_TAC(ARITH_RULE `4294967296 = 2 EXP (8 * 4)`) THEN
  ASM_REWRITE_TAC[READ_BYTES_MOD_LEN] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[GSYM DIMINDEX_32; VAL_MOD_REFL; WORD_VAL]);;

let EXTENSIONALLY_VALID_COMPONENT_BYTES32 = prove
 (`!a:(N tybit0)word. extensionally_valid_component (bytes32 a)`,
  SIMP_TAC[STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT;
           STRONGLY_VALID_COMPONENT_BYTES32]);;

let VALID_COMPONENT_BYTES32 = prove
 (`!a:(N tybit0)word. valid_component (bytes32 a)`,
  SIMP_TAC[STRONGLY_VALID_IMP_VALID_COMPONENT;
           STRONGLY_VALID_COMPONENT_BYTES32]);;

let WEAKLY_VALID_COMPONENT_BYTES32 = prove
 (`!a:(N tybit0)word. weakly_valid_component (bytes32 a)`,
  SIMP_TAC[VALID_IMP_WEAKLY_VALID_COMPONENT;
           VALID_COMPONENT_BYTES32]);;

let STRONGLY_VALID_COMPONENT_BYTES64 = prove
 (`!a:((N tybit0)tybit0)word.
      strongly_valid_component (bytes64 a)`,
  GEN_TAC THEN
  SUBGOAL_THEN `8 <= 2 EXP dimindex(:((N tybit0)tybit0))` ASSUME_TAC THENL
   [REWRITE_TAC[DIMINDEX_TYBIT0] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM(NUM_REDUCE_CONV `2 EXP 3`)] THEN
    REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
    MP_TAC(ISPEC `UNIV:N->bool` DIMINDEX_GE_1) THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:((N tybit0)tybit0)word`; `8`]
    EXTENSIONALLY_VALID_COMPONENT_BYTES) THEN
  MP_TAC(ISPECL [`a:((N tybit0)tybit0)word`; `8`] READ_WRITE_BYTES) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[strongly_valid_component; EXTENSIONALLY_VALID_COMPONENT] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[bytes64; READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[read; write; asword; through; VAL_WORD] THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBST1_TAC(ARITH_RULE `18446744073709551616 = 2 EXP (8 * 8)`) THEN
  ASM_REWRITE_TAC[READ_BYTES_MOD_LEN] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[GSYM DIMINDEX_64; VAL_MOD_REFL; WORD_VAL]);;

let EXTENSIONALLY_VALID_COMPONENT_BYTES64 = prove
 (`!a:((N tybit0)tybit0)word.
      extensionally_valid_component (bytes64 a)`,
  SIMP_TAC[STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT;
           STRONGLY_VALID_COMPONENT_BYTES64]);;

let VALID_COMPONENT_BYTES64 = prove
 (`!a:((N tybit0)tybit0)word. valid_component (bytes64 a)`,
  SIMP_TAC[STRONGLY_VALID_IMP_VALID_COMPONENT;
           STRONGLY_VALID_COMPONENT_BYTES64]);;

let WEAKLY_VALID_COMPONENT_BYTES64 = prove
 (`!a:((N tybit0)tybit0)word. weakly_valid_component (bytes64 a)`,
  SIMP_TAC[VALID_IMP_WEAKLY_VALID_COMPONENT;
           VALID_COMPONENT_BYTES64]);;

let STRONGLY_VALID_COMPONENT_BYTES128 = prove
 (`!a:((N tybit0)tybit0)word.
      strongly_valid_component (bytes128 a)`,
  GEN_TAC THEN
  SUBGOAL_THEN `16 <= 2 EXP dimindex(:((N tybit0)tybit0))` ASSUME_TAC THENL
   [REWRITE_TAC[DIMINDEX_TYBIT0] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM(NUM_REDUCE_CONV `2 EXP 4`)] THEN
    REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
    MP_TAC(ISPEC `UNIV:N->bool` DIMINDEX_GE_1) THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:((N tybit0)tybit0)word`; `16`]
    EXTENSIONALLY_VALID_COMPONENT_BYTES) THEN
  MP_TAC(ISPECL [`a:((N tybit0)tybit0)word`; `16`] READ_WRITE_BYTES) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[strongly_valid_component; EXTENSIONALLY_VALID_COMPONENT] THEN
  STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC
   [bytes128; READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[read; write; asword; through; VAL_WORD] THEN
  REWRITE_TAC[DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBST1_TAC(
    ARITH_RULE `340282366920938463463374607431768211456 = 2 EXP (8 * 16)`) THEN
  ASM_REWRITE_TAC[READ_BYTES_MOD_LEN] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[GSYM DIMINDEX_128; VAL_MOD_REFL; WORD_VAL]);;

let EXTENSIONALLY_VALID_COMPONENT_BYTES128 = prove
 (`!a:((N tybit0)tybit0)word.
      extensionally_valid_component (bytes128 a)`,
  SIMP_TAC[STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT;
           STRONGLY_VALID_COMPONENT_BYTES128]);;

let VALID_COMPONENT_BYTES128 = prove
 (`!a:((N tybit0)tybit0)word. valid_component (bytes128 a)`,
  SIMP_TAC[STRONGLY_VALID_IMP_VALID_COMPONENT;
           STRONGLY_VALID_COMPONENT_BYTES128]);;

let WEAKLY_VALID_COMPONENT_BYTES128 = prove
 (`!a:((N tybit0)tybit0)word. weakly_valid_component (bytes128 a)`,
  SIMP_TAC[VALID_IMP_WEAKLY_VALID_COMPONENT;
           VALID_COMPONENT_BYTES128]);;

let STRONGLY_VALID_COMPONENT_BYTES256 = prove
 (`!a:(((N tybit0)tybit0)tybit0)word.
      strongly_valid_component (bytes256 a)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `32 <= 2 EXP dimindex(:(((N tybit0)tybit0)tybit0))`
   ASSUME_TAC THENL
   [REWRITE_TAC[DIMINDEX_TYBIT0] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM(NUM_REDUCE_CONV `2 EXP 5`)] THEN
    REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
    MP_TAC(ISPEC `UNIV:N->bool` DIMINDEX_GE_1) THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:(((N tybit0)tybit0)tybit0)word`; `32`]
    EXTENSIONALLY_VALID_COMPONENT_BYTES) THEN
  MP_TAC(ISPECL [`a:(((N tybit0)tybit0)tybit0)word`; `32`]
    READ_WRITE_BYTES) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[strongly_valid_component; EXTENSIONALLY_VALID_COMPONENT] THEN
  STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC
   [bytes256; READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[read; write; asword; through; VAL_WORD] THEN
  REWRITE_TAC[DIMINDEX_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBST1_TAC(GSYM(NUM_REDUCE_CONV `2 EXP (8 * 32)`)) THEN
  ASM_REWRITE_TAC[READ_BYTES_MOD_LEN] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[GSYM DIMINDEX_256; VAL_MOD_REFL; WORD_VAL]);;

let EXTENSIONALLY_VALID_COMPONENT_BYTES256 = prove
 (`!a:(((N tybit0)tybit0)tybit0)word.
      extensionally_valid_component (bytes256 a)`,
  SIMP_TAC[STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT;
           STRONGLY_VALID_COMPONENT_BYTES256]);;

let VALID_COMPONENT_BYTES256 = prove
 (`!a:(((N tybit0)tybit0)tybit0)word. valid_component (bytes256 a)`,
  SIMP_TAC[STRONGLY_VALID_IMP_VALID_COMPONENT;
           STRONGLY_VALID_COMPONENT_BYTES256]);;

let WEAKLY_VALID_COMPONENT_BYTES256 = prove
 (`!a:(((N tybit0)tybit0)tybit0)word.
      weakly_valid_component (bytes256 a)`,
  SIMP_TAC[VALID_IMP_WEAKLY_VALID_COMPONENT;
           VALID_COMPONENT_BYTES256]);;

add_valid_component_thms
  [VALID_COMPONENT_BYTES8; VALID_COMPONENT_BYTES16;
   VALID_COMPONENT_BYTES32; VALID_COMPONENT_BYTES64;
   VALID_COMPONENT_BYTES128; VALID_COMPONENT_BYTES256];;

add_strongly_valid_component_thms
  [STRONGLY_VALID_COMPONENT_BYTES8; STRONGLY_VALID_COMPONENT_BYTES16;
   STRONGLY_VALID_COMPONENT_BYTES32; STRONGLY_VALID_COMPONENT_BYTES64;
   STRONGLY_VALID_COMPONENT_BYTES128; STRONGLY_VALID_COMPONENT_BYTES256];;

add_extensionally_valid_component_thms
  [EXTENSIONALLY_VALID_COMPONENT_BYTES8;
   EXTENSIONALLY_VALID_COMPONENT_BYTES16;
   EXTENSIONALLY_VALID_COMPONENT_BYTES32;
   EXTENSIONALLY_VALID_COMPONENT_BYTES64;
   EXTENSIONALLY_VALID_COMPONENT_BYTES128;
   EXTENSIONALLY_VALID_COMPONENT_BYTES256];;

add_weakly_valid_component_thms
  [WEAKLY_VALID_COMPONENT_BYTES8;
   WEAKLY_VALID_COMPONENT_BYTES16;
   WEAKLY_VALID_COMPONENT_BYTES32;
   WEAKLY_VALID_COMPONENT_BYTES64;
   WEAKLY_VALID_COMPONENT_BYTES128;
   WEAKLY_VALID_COMPONENT_BYTES256];;

(*** NB: the composites are better-behaved than plain "bytes".
 *** So when proving "valid_component" theorems by chaining, it
 *** makes sense not to expand them. Thus we don't put them in
 *** the aliases list.
 ***
 *** We probably will want to expand them for orthogonality proving.
 *** However all the memory-related orthogonality things need different
 *** handling anyway since they often need side-conditions
 ***)

let READ_MEMORY_BYTESIZED_SPLIT = prove
 (`(!m (x:A word) s. read (m :> bytes256 x) s =
            word_join (read (m :> bytes128 (word_add x (word 16))) s)
                      (read (m :> bytes128 x) s)) /\
   (!m (x:A word) s. read (m :> bytes128 x) s =
            word_join (read (m :> bytes64 (word_add x (word 8))) s)
                      (read (m :> bytes64 x) s)) /\
   (!m (x:A word) s. read (m :> bytes64 x) s =
            word_join (read (m :> bytes32 (word_add x (word 4))) s)
                      (read (m :> bytes32 x) s)) /\
   (!m (x:A word) s. read (m :> bytes32 x) s =
            word_join (read (m :> bytes16 (word_add x (word 2))) s)
                      (read (m :> bytes16 x) s)) /\
   (!m (x:A word) s. read (m :> bytes16 x) s =
            word_join (read (m :> bytes8 (word_add x (word 1))) s)
                      (read (m :> bytes8 x) s))`,
  REWRITE_TAC[GSYM VAL_EQ] THEN
  SIMP_TAC[VAL_WORD_JOIN_SIMPLE; DIMINDEX_256; DIMINDEX_128; DIMINDEX_64;
           DIMINDEX_32; DIMINDEX_16; DIMINDEX_8; ARITH] THEN
  REWRITE_TAC[bytes256; bytes128; bytes64; bytes32; bytes16; bytes8] THEN
  REWRITE_TAC[asword; through; read; READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_256; DIMINDEX_128; DIMINDEX_64; DIMINDEX_32;
              DIMINDEX_16; DIMINDEX_8] THEN
  REWRITE_TAC[ARITH_RULE
   `2 EXP 8 = 2 EXP (8 * 1) /\ 2 EXP 16 = 2 EXP (8 * 2) /\
    2 EXP 32 = 2 EXP (8 * 4) /\ 2 EXP 64 = 2 EXP (8 * 8) /\
    2 EXP 128 = 2 EXP (8 * 16) /\ 2 EXP 256 = 2 EXP (8 * 32)`] THEN
  SIMP_TAC[READ_BYTES_BOUND; MOD_LT] THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [ARITH_RULE `32 = 16 + 16 /\ 16 = 8 + 8 /\ 8 = 4 + 4 /\
                4 = 2 + 2 /\ 2 = 1 + 1`] THEN
  REWRITE_TAC[READ_BYTES_COMBINE] THEN ARITH_TAC);;

let READ_MEMORY_BYTESIZED_UNSPLIT = prove
 (`(!m (x:A word) s d.
      read (m :> bytes256 x) s = d <=>
      read (m :> bytes128 x) s = word_subword d (0,128) /\
      read (m :> bytes128 (word_add x (word 16))) s =
      word_subword d (128,128)) /\
   (!m (x:A word) s d.
      read (m :> bytes128 x) s = d <=>
      read (m :> bytes64 x) s = word_subword d (0,64) /\
      read (m :> bytes64 (word_add x (word 8))) s = word_subword d (64,64)) /\
   (!m (x:A word) s d.
      read (m :> bytes64 x) s = d <=>
      read (m :> bytes32 x) s = word_subword d (0,32) /\
      read (m :> bytes32 (word_add x (word 4))) s = word_subword d (32,32)) /\
   (!m (x:A word) s d.
      read (m :> bytes32 x) s = d <=>
      read (m :> bytes16 x) s = word_subword d (0,16) /\
      read (m :> bytes16 (word_add x (word 2))) s = word_subword d (16,16)) /\
   (!m (x:A word) s d.
      read (m :> bytes16 x) s = d <=>
      read (m :> bytes8 x) s = word_subword d (0,8) /\
      read (m :> bytes8 (word_add x (word 1))) s = word_subword d (8,8))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [READ_MEMORY_BYTESIZED_SPLIT] THEN
  ONCE_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[BIT_WORD_JOIN; BIT_WORD_SUBWORD] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC CONJ_ACI_RULE);;

let READ_MEMORY_TRIPLES_SPLIT = prove
 (`(!m (x:A word) s:S.
        read (m :> wbytes x) s :192 word =
        word_join (read (m :> bytes64 (word_add x (word 16))) s)
                  (word_join (read (m :> bytes64 (word_add x (word 8))) s)
                             (read (m :> bytes64 x) s):int128)) /\
   (!m (x:A word) s:S.
        read (m :> wbytes x) s :384 word =
        word_join (read (m :> bytes128 (word_add x (word 32))) s)
                  (word_join (read (m :> bytes128 (word_add x (word 16))) s)
                             (read (m :> bytes128 x) s):int256))`,
  REWRITE_TAC[GSYM VAL_EQ] THEN
  SIMP_TAC[VAL_WORD_JOIN_SIMPLE; DIMINDEX_64; DIMINDEX_128; DIMINDEX_256;
   ARITH; DIMINDEX_CONV `dimindex(:192)`; DIMINDEX_CONV `dimindex(:384)`] THEN
  REWRITE_TAC[BYTES64_WBYTES; BYTES128_WBYTES] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `24 = 8 + 8 + 8 /\ 48 = 16 + 16 + 16`] THEN
  REWRITE_TAC[READ_BYTES_COMBINE; WORD_ADD_ASSOC_CONSTS] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let WRITE_MEMORY_TRIPLES_SPLIT = prove
 (`(!m (x:A word) y s:S.
     valid_component m
      ==>  write (m :> wbytes x) (y:192 word) s =
           write (m :> bytes64 x) (word_subword y (0,64))
                 (write (m :> bytes64 (word_add x (word 8)))
                        (word_subword y (64,64))
                        (write (m :> bytes64 (word_add x (word 16)))
                               (word_subword y (128,64)) s))) /\
   (!m (x:A word) y s:S.
     valid_component m
      ==>  write (m :> wbytes x) (y:384 word) s =
           write (m :> bytes128 x) (word_subword y (0,128))
                 (write (m :> bytes128 (word_add x (word 16)))
                        (word_subword y (128,128))
                        (write (m :> bytes128 (word_add x (word 32)))
                               (word_subword y (256,128)) s)))`,
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[valid_component] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[bytes128; bytes64; wbytes; WRITE_COMPONENT_COMPOSE;
                  asword; through; read; write] THEN
  REWRITE_TAC[GSYM WRITE_BYTES_COMBINE; ARITH_ADD; ARITH_SUC] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_DIV_CONV)) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[VAL_BOUND_64; VAL_BOUND_128; MOD_LT; ARITH_RULE
   `(h < 2 EXP 64 /\ l < 2 EXP 64 ==> l + 2 EXP 64 * h < 2 EXP 128) /\
    (h < 2 EXP 128 /\ l < 2 EXP 128 ==> l + 2 EXP 128 * h < 2 EXP 256)`] THEN
  CONV_TAC WORD_BLAST);;

let READ_MEMORY_BYTES_TRIVIAL = prove(
  `forall (z:N word) (s:A) m. read (m :> bytes (z,0)) s = 0`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[READ_BYTES_TRIVIAL]);;

let PREFIX_BYTES_AS_SUBCOMPONENT = prove
 (`!(a:N word) m n.
        m <= n ==> ?c. bytes(a,m) = bytes(a,n) :> c`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[COMPONENT_EQ; EXISTS_COMPONENT] THEN
  EXISTS_TAC `\x. x MOD 2 EXP (8 * m)` THEN
  EXISTS_TAC
   `\y s. y MOD 2 EXP (8 * m) + 2 EXP (8 * m) * s DIV 2 EXP (8 * m) ` THEN
  CONJ_TAC THENL
   [ALL_TAC; GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `y:num`] THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `s:N word->byte` THEN
  ASM_SIMP_TAC[READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE; read; write;
               READ_BYTES_MOD; ARITH_RULE `m <= n ==> MIN n m = m`] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST1_TAC o
    GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  REWRITE_TAC[WRITE_BYTES_COMBINE] THEN
  REWRITE_TAC[READ_BYTES_DIV; ADD_SUB2] THEN
  REWRITE_TAC[REWRITE_RULE[extensionally_valid_component]
        EXTENSIONALLY_VALID_COMPONENT_BYTES]);;

let CONTAINED_BYTES_AS_SUBCOMPONENT_GEN = prove
 (`!(a:N word) b m n.
        val (word_sub a b) + m <= n /\
        n <= 2 EXP dimindex(:N)
        ==> ?c. bytes(a,m) = bytes(b,n) :> c`,
  let lemma = prove
   (`!(a:N word) m n.
          m + n <= 2 EXP dimindex(:N)
          ==> ?c. bytes(word_add a (word m),n) = bytes(a,m+n) :> c`,
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[COMPONENT_EQ; EXISTS_COMPONENT] THEN
    EXISTS_TAC `\x. x DIV 2 EXP (8 * m)` THEN
    EXISTS_TAC
     `\y:num s:num. s MOD 2 EXP (8 * m) + 2 EXP (8 * m) * y` THEN
    CONJ_TAC THENL
     [ALL_TAC; GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `y:num`] THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `s:N word->byte` THEN
    ASM_SIMP_TAC[READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE; read; write;
                 READ_BYTES_DIV; ADD_SUB2] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MOD_REFL] THEN
    REWRITE_TAC[WRITE_BYTES_COMBINE] THEN
    REWRITE_TAC[READ_BYTES_MOD; ARITH_RULE `MIN (m + n) m = m`] THEN
    MATCH_MP_TAC(MESON[]
     `read c s = read c s' /\ write c (read c s') s' = s'
      ==> s' = write c (read c s) s'`) THEN
    REWRITE_TAC[REWRITE_RULE[extensionally_valid_component]
          EXTENSIONALLY_VALID_COMPONENT_BYTES] THEN
    MATCH_MP_TAC(GSYM READ_WRITE_ORTHOGONAL_COMPONENTS) THEN
    REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES] THEN
    REWRITE_TAC[NONOVERLAPPING_MODULO] THEN
    ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
    REWRITE_TAC[NONOVERLAPPING_QFREE; WORD_VAL] THEN
    REWRITE_TAC[WORD_RULE `word_sub (word_add x y) x = y`] THEN
    STRIP_TAC THEN REWRITE_TAC[VAL_WORD] THEN
    SUBGOAL_THEN `m < 2 EXP dimindex(:N)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`b:N word`; `val(word_sub a b:N word)`; `m:num`] lemma) THEN
  REWRITE_TAC[WORD_VAL; WORD_RULE `word_add b (word_sub a b) = a`] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `d:(num,num)component` THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`b:N word`; `val(word_sub a b:N word) + m`; `n:num`]
        PREFIX_BYTES_AS_SUBCOMPONENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(num,num)component` SUBST1_TAC) THEN
  REWRITE_TAC[GSYM COMPONENT_COMPOSE_ASSOC] THEN MESON_TAC[]);;

let CONTAINED_BYTES_AS_SUBCOMPONENT = prove
 (`!(a:N word) b m n.
        n < 2 EXP dimindex(:N) /\
        contained (a,m) (b,n)
        ==> ?c. bytes(a,m) = bytes(b,n) :> c`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `m = 0` THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC[COMPONENT_EQ; bytes; FUN_EQ_THM;
                    READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
    EXISTS_TAC `rvalue 0:(num,num)component` THEN
    REWRITE_TAC[READ_RVALUE; WRITE_RVALUE] THEN
    REWRITE_TAC[REWRITE_RULE[extensionally_valid_component]
        EXTENSIONALLY_VALID_COMPONENT_BYTES];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC[LE_1; CONTAINED_QFREE] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[CONTAINED_BYTES_AS_SUBCOMPONENT_GEN; LT_IMP_LE]]);;

(* ------------------------------------------------------------------------- *)
(* State component corresponding to the head of a stack/list.                *)
(* ------------------------------------------------------------------------- *)

let top = new_definition
 `top = component((\l. HD l),(\h l. CONS h (TL l)))`;;

let VALID_COMPONENT_TOP = prove
 (`valid_component top`,
  REWRITE_TAC[valid_component; read; write; top; HD; TL]);;

add_valid_component_thms [VALID_COMPONENT_TOP];;

let WEAKLY_VALID_COMPONENT_TOP = prove
 (`weakly_valid_component top`,
  SIMP_TAC[VALID_IMP_WEAKLY_VALID_COMPONENT; VALID_COMPONENT_TOP]);;

add_weakly_valid_component_thms [WEAKLY_VALID_COMPONENT_TOP];;

let READ_TOP = prove
 (`read top = HD`,
  REWRITE_TAC[top; read; ETA_AX]);;

let READ_WRITE_TOP = prove
 (`(!h t. read top (CONS h t) = h) /\
   (!h a t. write top a (CONS h t) = CONS a t)`,
  REWRITE_TAC[read; write; top; HD; TL]);;

let READ_WRITE_SAME_TOP = prove
 (`!y s. read top (write top y s) = y`,
  REWRITE_TAC[read; write; top; HD]);;

add_component_read_write_thms [READ_WRITE_SAME_TOP];;

(* ------------------------------------------------------------------------- *)
(* Value modifier for functions.                                             *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("|->",(20,"right"));;

let valmod = new_definition
  `(x |-> a) (v:A->B) = \y. if y = x then a else v(y)`;;

let VALMOD = prove
 (`!v x y a. ((x |-> y) v) a = if a = x then y else v(a)`,
  REWRITE_TAC[valmod]);;

let VALMOD_BASIC = prove
 (`!v x y. (x |-> y) v x = y`,
  REWRITE_TAC[valmod]);;

let VALMOD_VALMOD_BASIC = prove
 (`!v a b x. (x |-> a) ((x |-> b) v) = (x |-> a) v`,
  REWRITE_TAC[valmod; FUN_EQ_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let VALMOD_REPEAT = prove
 (`!v x. (x |-> v(x)) v = v`,
  REWRITE_TAC[valmod; FUN_EQ_THM] THEN MESON_TAC[]);;

let FORALL_VALMOD = prove
 (`!x. (!v a. P((x |-> a) v)) = (!v. P v)`,
  MESON_TAC[VALMOD_REPEAT]);;

let VALMOD_SWAP = prove
 (`!v x y a b.
     ~(x = y) ==> ((x |-> a) ((y |-> b) v) = (y |-> b) ((x |-> a) v))`,
  REWRITE_TAC[valmod; FUN_EQ_THM] THEN MESON_TAC[]);;

let SELECT_VALMOD = prove
 (`!f x. (@y. (x |-> y) f = f) = f(x)`,
  REWRITE_TAC[valmod; FUN_EQ_THM] THEN MESON_TAC[]);;

let VALMOD_REFL = prove
 (`(x |-> a) f = f <=> f(x) = a`,
  REWRITE_TAC[valmod; FUN_EQ_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Interaction between component formalization and valmod.                   *)
(* ------------------------------------------------------------------------- *)

let READ_ELEMENT_VALMOD = prove
 (`!v i j k. read (element i) ((j |-> k) v) =
             if i = j then k else read (element i) v`,
  REWRITE_TAC[valmod; read; element]);;

let WRITE_ELEMENT_VALMOD = prove
 (`!v i j k p.
        write (element i) p ((j |-> k) v) =
        if i = j then (i |-> p) v else (j |-> k) (write (element i) p v)`,
  REWRITE_TAC[write; element; valmod; FUN_EQ_THM] THEN
  MESON_TAC[]);;

let WRITE_ELEMENT_ABS = prove
 (`write (element i) k (\j. p) = (i |-> k) (\j. p)`,
  REWRITE_TAC[FUN_EQ_THM; write; element; valmod]);;

(* ------------------------------------------------------------------------- *)
(* Canonize a state component using aliases and right-association.           *)
(* ------------------------------------------------------------------------- *)


let component_canon_conv_cache: (term * thm) list ref = ref [];;

let (COMPONENT_CANON_CONV:conv),add_component_alias_thms =
  let mk_conv thms =
    GEN_REWRITE_CONV TOP_DEPTH_CONV (GSYM COMPONENT_COMPOSE_ASSOC::thms) in
  let conv = ref (mk_conv !component_alias_thms) in
  (fun tm ->
    if is_const tm then
      try assoc tm !component_canon_conv_cache
      with Failure _ ->
        let thnew = !conv tm in
        component_canon_conv_cache := (tm,thnew)::!component_canon_conv_cache;
        thnew
    else !conv tm),
  fun l ->
    let new_thms = union l (!component_alias_thms) in
    component_alias_thms := new_thms;
    conv := mk_conv !component_alias_thms;
    component_canon_conv_cache := [] ;;


(* ------------------------------------------------------------------------- *)
(* Tool to produce "|- valid_component c" theorems.                          *)
(* ------------------------------------------------------------------------- *)

let VALID_COMPONENT_RULE =
  let rec rule tm =
    match tm with
      Comb(Const("bitelement",_),_) ->
        let th = PART_MATCH (rand o rand) VALID_COMPONENT_BITELEMENT tm in
        let ctm = lhand(concl th) in
        MP th (EQT_ELIM((GEN_REWRITE_CONV RAND_CONV (!word_sizes) THENC
                        NUM_LT_CONV) ctm))
    | Comb(Comb(Const(":>",_),c1),c2) ->
          MATCH_MP VALID_COMPONENT_COMPOSE (CONJ (rule c1) (rule c2))
    | _ -> tryfind (fun th -> PART_MATCH rand th tm)
                   (!valid_component_thms) in
  fun tm ->
    let eth = COMPONENT_CANON_CONV tm in
    let th = rule(rand(concl eth)) in
    GEN_REWRITE_RULE RAND_CONV [SYM eth] th;;

let VALID_COMPONENT_CONV tm =
  match tm with
    Comb(Const("valid_component",_),c) -> VALID_COMPONENT_RULE c
  | _ -> failwith "VALID_COMPONENT_CONV";;

(* ------------------------------------------------------------------------- *)
(* Similar one for "|- weakly_valid_component".                              *)
(* ------------------------------------------------------------------------- *)

let WEAKLY_VALID_COMPONENT_RULE =
  let rec rule tm =
    match tm with
      Comb(Const("bitelement",_),_) ->
        let th = PART_MATCH (rand o rand)
                   WEAKLY_VALID_COMPONENT_BITELEMENT tm in
        let ctm = lhand(concl th) in
        MP th (EQT_ELIM((GEN_REWRITE_CONV RAND_CONV (!word_sizes) THENC
                        NUM_LT_CONV) ctm))
    | Comb(Comb(Const(":>",_),c1),c2) ->
          MATCH_MP WEAKLY_VALID_COMPONENT_COMPOSE
             (CONJ (VALID_COMPONENT_RULE c1) (rule c2))
    | _ -> tryfind (fun th -> PART_MATCH rand th tm)
                   (!weakly_valid_component_thms) in
  fun tm ->
    let eth = COMPONENT_CANON_CONV tm in
    let th = rule(rand(concl eth)) in
    GEN_REWRITE_RULE RAND_CONV [SYM eth] th;;

let WEAKLY_VALID_COMPONENT_CONV tm =
  match tm with
    Comb(Const("weakly_valid_component",_),c) -> WEAKLY_VALID_COMPONENT_RULE c
  | _ -> failwith "WEAKLY_VALID_COMPONENT_CONV";;

(* ------------------------------------------------------------------------- *)
(* Similar one for "|- strongly_valid_component c"                           *)
(* ------------------------------------------------------------------------- *)

let STRONGLY_VALID_COMPONENT_RULE =
  let rec rule tm =
    match tm with
      Comb(Const("bitelement",_),_) ->
        let th = PART_MATCH (rand o rand)
                   STRONGLY_VALID_COMPONENT_BITELEMENT tm in
        let ctm = lhand(concl th) in
        MP th (EQT_ELIM((GEN_REWRITE_CONV RAND_CONV (!word_sizes) THENC
                        NUM_LT_CONV) ctm))
    | Comb(Comb(Const(":>",_),c1),c2) ->
          MATCH_MP STRONGLY_VALID_COMPONENT_COMPOSE (CONJ (rule c1) (rule c2))
    | _ -> tryfind (fun th -> PART_MATCH rand th tm)
                   (!strongly_valid_component_thms) in
  fun tm ->
    let eth = COMPONENT_CANON_CONV tm in
    let th = rule(rand(concl eth)) in
    GEN_REWRITE_RULE RAND_CONV [SYM eth] th;;

let STRONGLY_VALID_COMPONENT_CONV tm =
  match tm with
    Comb(Const("strongly_valid_component",_),c) ->
      STRONGLY_VALID_COMPONENT_RULE c
  | _ -> failwith "STRONGLY_VALID_COMPONENT_CONV";;

(* ------------------------------------------------------------------------- *)
(* And also "|- extensionally_valid_component c"                             *)
(* ------------------------------------------------------------------------- *)

let EXTENSIONALLY_VALID_COMPONENT_RULE =
  let rec rule tm =
    match tm with
      Comb(Const("bitelement",_),_) ->
        let th = PART_MATCH (rand o rand)
                   EXTENSIONALLY_VALID_COMPONENT_BITELEMENT tm in
        let ctm = lhand(concl th) in
        MP th (EQT_ELIM((GEN_REWRITE_CONV RAND_CONV (!word_sizes) THENC
                        NUM_LT_CONV) ctm))
    | Comb(Comb(Const(":>",_),ltm),rtm) ->
        let lth = STRONGLY_VALID_COMPONENT_RULE ltm
        and rth = rule rtm in
        MATCH_MP EXTENSIONALLY_VALID_COMPONENT_COMPOSE (CONJ lth rth)
    | _ -> tryfind (fun th -> PART_MATCH rand th tm)
                   (!extensionally_valid_component_thms) in
  fun tm ->
    (try let eth = COMPONENT_CANON_CONV tm in
         let th = rule(rand(concl eth)) in
         GEN_REWRITE_RULE RAND_CONV [SYM eth] th
     with Failure _ ->
        let ith = ISPEC tm STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT in
        MP ith (STRONGLY_VALID_COMPONENT_CONV (lhand(concl ith)))
    );;

let EXTENSIONALLY_VALID_COMPONENT_CONV tm =
  match tm with
    Comb(Const("extensionally_valid_component",_),c) ->
      EXTENSIONALLY_VALID_COMPONENT_RULE c
  | _ -> failwith "EXTENSIONALLY_VALID_COMPONENT_CONV";;

(* ------------------------------------------------------------------------- *)
(* Tool to produce "|- !y s. read c (write c y s) = y" theorems              *)
(* ------------------------------------------------------------------------- *)

let READ_WRITE_SAME_RULE =
  let mrule tm th =
    let vtm = lhand(lhand(snd(strip_forall(concl th)))) in
    let iz = term_match [] vtm tm in
    INSTANTIATE iz th in
  let rec rule tm =
    match tm with
      Comb(Const("bitelement",_),_) ->
        let th = PART_MATCH (lhand o lhand o snd o strip_forall o rand)
                            READ_WRITE_BITELEMENT tm in
        let ctm = lhand(concl th) in
        MP th (EQT_ELIM((GEN_REWRITE_CONV RAND_CONV (!word_sizes) THENC
                        NUM_LT_CONV) ctm))
    | Comb(Comb(Const(":>",_),c1),c2) ->
          MATCH_MP READ_WRITE_ORTHOGONAL_COMPOSE_L (CONJ (rule c1) (rule c2))
    | _ -> tryfind (mrule tm)
                (!component_read_write_thms) in
  fun tm ->
    let eth = COMPONENT_CANON_CONV tm in
    let th = rule(rand(concl eth)) in
    (GEN_REWRITE_RULE
      (BINDER_CONV o BINDER_CONV o LAND_CONV o LAND_CONV) [SYM eth] o
     GEN_REWRITE_RULE
      (BINDER_CONV o BINDER_CONV o LAND_CONV o
       RAND_CONV o RATOR_CONV o LAND_CONV) [SYM eth]) th;;

(* ------------------------------------------------------------------------- *)
(* Tool to produce "|- orthogonal_component c1 c2" theorems.                 *)
(* Further down we define a more powerful tactic without SIMPLE.             *)
(* This only deals with relatively easy memory region containments of the    *)
(* form "base + c1" and "base + c2" for constant words c1 and c2, with       *)
(* bytes64/bytes128. This is mainly for the benefit of ARM STP which has two *)
(* writes. Otherwise more sophisticated ones are deferred to below.          *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_COMPONENTS_BYTES64_TAC =
  let pth = prove
   (`!(a:N word) m n.
          8 <= val(word_sub (word m) (word n):N word) /\
          8 <= val(word_sub (word n) (word m):N word)
          ==> orthogonal_components
                (bytes64 (word_add a (word m)))
                (bytes64 (word_add a (word n)))`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[bytes64] THEN
    MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_LEFT THEN
    REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES] THEN
    REWRITE_TAC[VAL_WORD_ADD; NONOVERLAPPING_MODULO_MOD2] THEN
    MATCH_MP_TAC NONOVERLAPPING_MODULO_OFFSET_SIMPLE_BOTH THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_CASES]) THEN
    MP_TAC(ISPEC `word m:N word` VAL_BOUND) THEN
    MP_TAC(ISPEC `word n:N word` VAL_BOUND) THEN
    ASM_ARITH_TAC)
  and qth = MESON[WORD_ADD_0]
    `(orthogonal_components
       (bytes64 (a:N word)) (bytes64 (word_add a (word n))) <=>
      orthogonal_components
       (bytes64 (word_add a (word 0))) (bytes64 (word_add a (word n)))) /\
     (orthogonal_components
       (bytes64 (word_add a (word n))) (bytes64 a) <=>
      orthogonal_components
       (bytes64 (word_add a (word n))) (bytes64 (word_add a (word 0))))`
  (* rth deals with the case when (m, n) in pth is of a form (x + y, x),
     (x, x + y) or (x + y, x + z). This helps ORTHOGONAL_COMPONENTS_BYTES64_TAC
     solve the case when the address given to ARM STP is an expression
     `word_add (word x0) (word x1)`, and the STP offset +8 is combined with
     x1, meaning that (m, n) = (x1, x1 + 8). If x1 = x1' + const, '+8' is
     again combined with '+ const', making
     (m, n) = (x' + const, x' + (const+8)). *)
  and rth = WORD_RULE
     `word_sub (word (x + y)) (word x):N word = word y /\
      word_sub (word x) (word (x + y)):N word = word_neg (word y) /\
      word_sub (word (x + y)) (word (x + z)):N word =
      word_sub (word y) (word z)` in
  GEN_REWRITE_TAC TRY_CONV [qth] THEN
  MATCH_MP_TAC pth THEN REWRITE_TAC[rth] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;;

let ORTHOGONAL_COMPONENTS_BYTES128_TAC =
  let pth = prove
   (`!(a:N word) m n.
          16 <= val(word_sub (word m) (word n):N word) /\
          16 <= val(word_sub (word n) (word m):N word)
          ==> orthogonal_components
                (bytes128 (word_add a (word m)))
                (bytes128 (word_add a (word n)))`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[bytes128] THEN
    MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_LEFT THEN
    REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES] THEN
    REWRITE_TAC[VAL_WORD_ADD; NONOVERLAPPING_MODULO_MOD2] THEN
    MATCH_MP_TAC NONOVERLAPPING_MODULO_OFFSET_SIMPLE_BOTH THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_CASES]) THEN
    MP_TAC(ISPEC `word m:N word` VAL_BOUND) THEN
    MP_TAC(ISPEC `word n:N word` VAL_BOUND) THEN
    ASM_ARITH_TAC)
  and qth = MESON[WORD_ADD_0]
    `(orthogonal_components
       (bytes128 (a:N word)) (bytes128 (word_add a (word n))) <=>
      orthogonal_components
       (bytes128 (word_add a (word 0))) (bytes128 (word_add a (word n)))) /\
     (orthogonal_components
       (bytes128 (word_add a (word n))) (bytes128 a) <=>
      orthogonal_components
       (bytes128 (word_add a (word n))) (bytes128 (word_add a (word 0))))`
  (* rth deals with the case when (m, n) in pth is of a form (x + y, x),
     (x, x + y) or (x + y, x + z). This helps ORTHOGONAL_COMPONENTS_BYTES128_TAC
     solve the case when the address given to ARM STP is an expression
     `word_add (word x0) (word x1)`, and the STP offset +16 is combined with
     x1, meaning that (m, n) = (x1, x1 + 16). If x1 = x1' + const, '+16' is
     again combined with '+ const', making
     (m, n) = (x' + const, x' + (const+16)). *)
  and rth = WORD_RULE
     `word_sub (word (x + y)) (word x):N word = word y /\
      word_sub (word x) (word (x + y)):N word = word_neg (word y) /\
      word_sub (word (x + y)) (word (x + z)):N word =
      word_sub (word y) (word z)` in
  GEN_REWRITE_TAC TRY_CONV [qth] THEN
  MATCH_MP_TAC pth THEN REWRITE_TAC[rth] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;;

let SIMPLE_ORTHOGONAL_COMPONENTS_TAC =
  let tac =
    (MAP_FIRST MATCH_ACCEPT_TAC
      (CONJUNCTS ORTHOGONAL_COMPONENTS_RVALUE)) ORELSE
    (MATCH_MP_TAC ORTHOGONAL_COMPONENTS_BITELEMENT THEN
     CONV_TAC(RAND_CONV NUM_EQ_CONV) THEN
     GEN_REWRITE_TAC I [TAUT `~F <=> T`]) ORELSE
    (MATCH_MP_TAC ORTHOGONAL_COMPONENTS_ELEMENT THEN
      (CONV_TAC(RAND_CONV(WORD_EQ_CONV ORELSEC NUM_EQ_CONV)) THEN
       GEN_REWRITE_TAC I [TAUT `~F <=> T`])) ORELSE
    MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT THEN CONJ_TAC THENL
     [CONV_TAC VALID_COMPONENT_CONV; ALL_TAC] ORELSE
    MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_LEFT ORELSE
    MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_LEFT ORELSE
    MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_RIGHT ORELSE
    MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_LEFT in
  fun g ->
    (CONV_TAC(BINOP_CONV COMPONENT_CANON_CONV) THEN
     REPEAT
      (W(fun (asl,w) ->
        match w with
        | Comb(Comb(Const("orthogonal_components",_), Const (_,_)), Const (_,_)) ->
          MAP_FIRST MATCH_ACCEPT_TAC (!component_orthogonality_thms)
        | _ -> tac ORELSE
               ORTHOGONAL_COMPONENTS_BYTES64_TAC ORELSE
               ORTHOGONAL_COMPONENTS_BYTES128_TAC))) g;;

(* A cache that stores `orthogonal_components x y` theorems.
   `assoc y !(assoc x !orthogonal_components_conv_cache)` must return the
   theorem, if the entry exists. *)
let orthogonal_components_conv_cache:
    (term * ((term * thm) list ref)) list ref = ref [];;

(* A custom cache that can be installed by a user. *)
let orthogonal_components_conv_custom_cache:
    ((term * term * (unit -> thm)) -> thm option) ref = ref (fun _ -> None);;

let ORTHOGONAL_COMPONENTS_CONV tm =
  try
    let lhs,rhs = dest_binary "orthogonal_components" tm in
    let eval () = prove(tm,SIMPLE_ORTHOGONAL_COMPONENTS_TAC) in
    (* Use cache if lhs and rhs are constants, e.g., `PC` or `X1`. *)
    if is_const lhs && is_const rhs then
      try
        let lref = assoc lhs !orthogonal_components_conv_cache in
        try assoc rhs !lref
        with Failure _ -> let newth = eval() in lref := (rhs, newth)::!lref;
          newth
      with Failure _ -> let newth = eval() in
        orthogonal_components_conv_cache := (lhs, ref [(rhs,newth)])::!orthogonal_components_conv_cache;
        newth
    else begin
      match !orthogonal_components_conv_custom_cache (lhs,rhs,eval) with
      | Some th -> th
      | None -> eval()
    end
  with Failure _ -> failwith "ORTHOGONAL_COMPONENTS_CONV: unknown term";;

let ORTHOGONAL_COMPONENTS_RULE2 tm1 tm2 =
  ORTHOGONAL_COMPONENTS_CONV(list_mk_icomb "orthogonal_components" [tm1;tm2]);;

(* ------------------------------------------------------------------------- *)
(* Slightly ad hoc tactic to do "simple" linear arithmetic: pick out         *)
(* "environmental" assumptions with relevance to natural number arithmetic.  *)
(* ------------------------------------------------------------------------- *)

let (SIMPLE_ARITH_TAC:tactic) =
  let numty = `:num` in
  let is_num_relop tm =
    exists (fun op -> is_binary op tm &&
                      (let x,_ = dest_binary op tm in type_of x = numty))
           ["=";"<";"<=";">";">="]
  and avoiders = ["lowdigits"; "highdigits"; "bigdigit";
                  "read"; "write"; "val"; "word"] in
  let avoiderp tm =
    match tm with Const(n,_) -> mem n avoiders | _ -> false in
  let filtered tm =
    (is_num_relop tm || (is_neg tm && is_num_relop (dest_neg tm))) &&
    not(can (find_term avoiderp) tm) in
  let tweak = GEN_REWRITE_RULE TRY_CONV [ARITH_RULE `~(n = 0) <=> 1 <= n`] in
  W(fun (asl,w) ->
    let asl' = filter (fun (_,th) -> filtered(concl th)) asl in
    MAP_EVERY (MP_TAC o tweak o snd) asl' THEN CONV_TAC ARITH_RULE);;

let SIMPLE_ARITH_RULE t = prove (t, SIMPLE_ARITH_TAC);;
let ASM_SIMPLE_ARITH_RULE t =
  SUBGOAL_THEN t ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Prove val(word n:int64) = n where it's just simple arithmetic.            *)
(* ------------------------------------------------------------------------- *)

let VAL_INT64_TAC =
  let pth = prove
   (`!n. n < 18446744073709551616 ==> val(word n:int64) = n`,
    REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN ARITH_TAC) in
  fun t -> MP_TAC(SPEC t pth) THEN
           ANTS_TAC THENL [SIMPLE_ARITH_TAC THEN NO_TAC; DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* Automatically prove containment of regions                                *)
(* ------------------------------------------------------------------------- *)

let CONTAINED_TAC =
  GEN_REWRITE_TAC I [GSYM CONTAINED_MODULO_MOD2] THEN
  GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o LAND_CONV o TOP_DEPTH_CONV)
   [VAL_WORD_ADD; VAL_WORD] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(BINOP_CONV(LAND_CONV MOD_DOWN_CONV)) THEN
  GEN_REWRITE_TAC I [CONTAINED_MODULO_MOD2] THEN
  ((GEN_REWRITE_TAC I [CONTAINED_MODULO_REFL] THEN
    SIMPLE_ARITH_TAC) ORELSE
   (MATCH_MP_TAC CONTAINED_MODULO_OFFSET_SIMPLE THEN
    SIMPLE_ARITH_TAC) ORELSE
   (MATCH_MP_TAC CONTAINED_MODULO_SIMPLE THEN SIMPLE_ARITH_TAC));;

(* ------------------------------------------------------------------------- *)
(* An additional lemma for manual nonoverlap proofs.                         *)
(* ------------------------------------------------------------------------- *)

let NONOVERLAPPING_MODULO_OFFSET_BOTH = prove
 (`!(z:N word) m i n j.
        m + i <= n /\ n + j <= m + 2 EXP dimindex(:N) \/
        n + j <= m /\ m + i <= n + 2 EXP dimindex(:N)
        ==> nonoverlapping_modulo (2 EXP dimindex(:N))
             (val(word_add z (word m)),i) (val(word_add z (word n)),j)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[NONOVERLAPPING_MODULO_MOD2] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_OFFSET_SIMPLE_BOTH THEN
  ASM_REWRITE_TAC[]);;

let NONOVERLAPPING_MODULO_64_OFFSET_BOTH =
  CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV)
    (INST_TYPE [`:64`,`:N`] NONOVERLAPPING_MODULO_OFFSET_BOTH);;

(* ------------------------------------------------------------------------- *)
(* Eliminate nonoverlapping_modulo in favour of nonoverlapping.              *)
(* Evetually we'll restructure all the proofs to keep this anyway.           *)
(* ------------------------------------------------------------------------- *)

let NONOVERLAP_REVERT_CONV =
  let pth = prove
   (`!(base1:N word) base2 len1 len2.
        nonoverlapping_modulo (2 EXP dimindex(:N))
          (val base1,len1) (val base2,len2) <=>
        nonoverlapping (base1,len1) (base2,len2)`,
     REWRITE_TAC[nonoverlapping])
  and qth = NONOVERLAPPING_MODULO
  and qth64 = prove
   (`!base1 base2 len1 len2.
        nonoverlapping_modulo (2 EXP 64) (base1,len1) (base2,len2) <=>
        nonoverlapping (word base1:int64,len1) (word base2:int64,len2)`,
    REWRITE_TAC[nonoverlapping; NONOVERLAPPING_CLAUSES; DIMINDEX_64]) in
  GEN_REWRITE_CONV I [pth] ORELSEC
  (GEN_REWRITE_CONV I [qth;qth64] THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV [WORD_VAL]);;

(* ------------------------------------------------------------------------- *)
(* Normalize as word_add base (iword x), even by introducing iword(&0).      *)
(* ------------------------------------------------------------------------- *)

let INORMALIZE_RELATIVE_ADDRESS_CONV =
  let CHECK_REMAINDERED_CONV = ALL_CONV o check(vfree_in `rem`) in
  let trivconv = GEN_REWRITE_CONV I
    [WORD_RULE `z:N word = word_add z (iword(&0))`]
  and initconv =
   GEN_REWRITE_CONV TOP_DEPTH_CONV
     [WORD_ADD; IWORD_INT_ADD; WORD_VAL; GSYM WORD_ADD_ASSOC;
      WORD_RULE `word_sub x y:N word = word_add x (word_neg y)`]
  and mainconv =
    GEN_REWRITE_CONV DEPTH_CONV [VAL_WORD] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV
     [GSYM IWORD_INT_ADD; WORD_IWORD;
      GSYM IWORD_INT_NEG; GSYM IWORD_INT_MUL] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV
     [GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM] THENC
    TRY_CONV(CHECK_REMAINDERED_CONV THENC
             GEN_REWRITE_CONV I [GSYM IWORD_REM_SIZE] THENC
             RAND_CONV INT_REM_DOWN_CONV THENC
             GEN_REWRITE_CONV I [IWORD_REM_SIZE]) in
  let postconv tm =
    match tm with
      Var(_,_)
    | Comb(Const("word",_),_) -> trivconv tm
    | Comb(Comb(Const("word_add",_),_),_) -> RAND_CONV mainconv tm
    | _ -> mainconv tm in
  initconv THENC postconv;;

(* ------------------------------------------------------------------------- *)
(* Derive nonoverlapping-justifying reductions to arithmetic from a          *)
(* given context of nonoverlapping hypotheses, if any. In all cases          *)
(* add a theorem for the case where both regions have the same base.         *)
(* ------------------------------------------------------------------------- *)

let NONOVERLAPPING_DRIVERS =
  let pth = prove
   (`!(base1:N word) base2 off1 off2 len1 len2 off1' off2' len1' len2'.
          nonoverlapping (word_add base1 (iword off1),len1)
                         (word_add base2 (iword off2),len2)
          ==> (0 < len1'
               ==> &0 <= off1' - off1 /\ (off1' - off1) + &len1' <= &len1) /\
              (0 < len2'
               ==> &0 <= off2' - off2 /\ (off2' - off2) + &len2' <= &len2)
              ==> nonoverlapping (word_add base1 (iword off1'),len1')
                                 (word_add base2 (iword off2'),len2')`,
    REPEAT GEN_TAC THEN DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE
     [TAUT `p /\ q /\ r ==> s <=> q /\ r ==> p ==> s`]
          NONOVERLAPPING_SUBREGIONS) THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTAINED_SIMPLE THEN
    ASM_REWRITE_TAC[]) in
  let pth' = prove
   (`!(base1:N word) base2 off1 off2 len1 len2 off1' off2' len1' len2'.
          word_add base1 (iword off1) = word_add base2 (iword off2) \/
          nonoverlapping (word_add base1 (iword off1),len1)
                         (word_add base2 (iword off2),len2)
          ==> (0 < len1'
               ==> &0 <= off1' - off1 /\ (off1' - off1) + &len1' <= &len1) /\
              (0 < len2'
               ==> &0 <= off2' - off2 /\ (off2' - off2) + &len2' <= &len2) /\
              (0 < len1' /\ 0 < len2'
               ==> &len2' <= off1' - (off1 - off2 + off2') /\
                    off1' - (off1 - off2 + off2') + &len1'
                    <= &2 pow dimindex(:N) \/
                   &len1' <= (off1 - off2 + off2') - off1' /\
                   (off1 - off2 + off2') - off1' + &len2'
                   <= &2 pow dimindex(:N))
              ==> nonoverlapping (word_add base1 (iword off1'),len1')
                                 (word_add base2 (iword off2'),len2')`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[pth]] THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (WORD_RULE
     `word_add b1 (iword off1) = word_add b2 (iword off2)
      ==> b2 = word_add b1 (iword(off1 - off2))`)) THEN
    REWRITE_TAC[WORD_RULE
     `word_add (word_add b (iword x)) (iword y) =
      word_add b (iword(x + y))`] THEN
    MATCH_MP_TAC NONOVERLAPPING_SIMPLE THEN ASM_REWRITE_TAC[]) in
  let pat1 =
   can (term_match [] `nonoverlapping (a:N word,m) (b,n)`)
  and pat2 =
   can (term_match []
     `a:N word = b \/ nonoverlapping (a,m) (b,n)`)
  and rule1 = MATCH_MP pth
  and rule2 = MATCH_MP pth'
  and postrule =
    GEN_REWRITE_RULE TOP_DEPTH_CONV
     [GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_ADD;
      INT_SUB_RZERO; INT_ADD_LID; INT_ADD_RID] in
  let OVERLAPPING_DRIVER th =
    let th1 = CONV_RULE (ONCE_DEPTH_CONV NONOVERLAP_REVERT_CONV) th in
    let tm = concl th1 in
    let th2 =
      if pat1 tm then
          rule1 (CONV_RULE
           (BINOP_CONV (LAND_CONV INORMALIZE_RELATIVE_ADDRESS_CONV)) th1)
      else if pat2 tm then
          rule2 (CONV_RULE
           (BINOP2_CONV (BINOP_CONV INORMALIZE_RELATIVE_ADDRESS_CONV)
              (BINOP_CONV (LAND_CONV INORMALIZE_RELATIVE_ADDRESS_CONV))) th1)
      else failwith "OVERLAPPING_DRIVER" in
    postrule th2 in
  fun thl ->
    let ths = mapfilter OVERLAPPING_DRIVER thl in
    let ths' = map (PURE_ONCE_REWRITE_RULE[NONOVERLAPPING_SYM]) ths in
    NONOVERLAPPING_SIMPLE :: ths @ ths';;

(* ------------------------------------------------------------------------- *)
(* Simple conversion to integer versus natural number properties.            *)
(* ------------------------------------------------------------------------- *)

let INT_OF_NUM_CONV =
  TOP_DEPTH_CONV DIMINDEX_CONV THENC
  GEN_REWRITE_CONV TOP_DEPTH_CONV
   [ARITH_RULE `~(n = 0) <=> 1 <= n`] THENC
  GEN_REWRITE_CONV TOP_DEPTH_CONV
   [LT_MULT; ARITH_RULE `c:num < a - b <=> c + b < a`] THENC
  GEN_REWRITE_CONV TOP_DEPTH_CONV
   [GSYM INT_OF_NUM_DIV; GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_SUC;
    ARITH_RULE `!m n. &(m - n):int = max (&0) (&m - &n)`;
    ARITH_RULE `!n. &(PRE n):int = max (&0) (&n - &1)`;
    GSYM INT_OF_NUM_CLAUSES] THENC
  NUM_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* Filter away assumptions other than natural number predicates and any      *)
(* involving various other constructs, notably the "read" function. The idea *)
(* is to keep only those that might be involved in address calculation. When *)
(* a theorem passes the filter, normalize arithmetic to be on Z not N.       *)
(* ------------------------------------------------------------------------- *)

let FILTER_CANONIZE_ASSUMPTIONS =
  let numty = `:num` in
  let is_num_relop tm =
    exists (fun op -> is_binary op tm &&
                      (let x,_ = dest_binary op tm in type_of x = numty))
           ["=";"<";"<=";">";">="]
  and avoiders = ["lowdigits"; "highdigits"; "bigdigit";
                  "read"; "write"; "word"] in
  let avoiderp tm =
    match tm with
      Comb(Comb(Const("DIV",_),_),m) -> not(is_numeral m)
    | Comb(Comb(Const("MOD",_),_),m) -> not(is_numeral m)
    | Comb(Comb(Const("EXP",_),_),m) -> not(frees m = [])
    | Const(n,_) -> mem n avoiders
    | _ -> false in
  let filtered tm =
    (is_num_relop tm || (is_neg tm && is_num_relop(rand tm))) &&
    not(can (find_term avoiderp) tm) in
  let FILTER_CANONIZE_ASSUMPTION th =
    if filtered(concl th) then CONV_RULE INT_OF_NUM_CONV th
    else failwith "FILTER_CANONIZE_ASSUMPTION" in
  mapfilter FILTER_CANONIZE_ASSUMPTION;;

(* ------------------------------------------------------------------------- *)
(* Automatically prove nonoverlapping of regions. In the rule version, the   *)
(* first argument is a pair: the contextual lemmas driving backchaining,     *)
(* and the current arithmetical assumptions.                                 *)
(* ------------------------------------------------------------------------- *)

let NONOVERLAPPING_RULE =
  let SIMPLE_INT_POS_RULE =
    let rule_mul = PART_MATCH rand INT_LE_MUL
    and rule_add = PART_MATCH rand INT_LE_ADD
    and rule_max = PART_MATCH I (INT_ARITH `&0:int <= max (&0) x`)
    and rule_num = PART_MATCH I INT_POS in
    let rec rule tm =
      try rule_max tm with Failure _ ->
      try rule_num tm with Failure _ ->
      let ith = (try rule_mul tm with Failure _ -> rule_add tm) in
      let ltm,rtm = dest_conj(lhand(concl ith)) in
      MP ith (CONJ (rule ltm) (rule rtm)) in
    rule in
  let CONTEXT_INT_ARITH ths tm =
    try SIMPLE_INT_POS_RULE tm with Failure _ ->
    try INT_ARITH tm with Failure _ ->
    if ths = [] then failwith "CONTEXT_INT_ARITH_RULE" else
    let tm' = itlist (curry mk_imp o concl) ths tm in
    rev_itlist (C MP) ths (INT_ARITH tm') in
  let pth_mul = prove
   (`0 < a * b <=> &(a * b):int = &a * &b /\ 0 < a /\ 0 < b`,
    REWRITE_TAC[INT_OF_NUM_CLAUSES; LT_MULT])
  and pth_sub = prove
   (`c < a - b <=> &(a - b):int = &a - &b /\ c + b < a`,
    ARITH_TAC) in
  let rule_mul = GEN_REWRITE_RULE I [pth_mul]
  and rule_sub = GEN_REWRITE_RULE I [pth_sub] in
  let rec DECOMP_LT (dun,eqs,todo) =
    match todo with
      [] -> (map (CONV_RULE INT_OF_NUM_CONV) dun,eqs)
    | th::oths ->
       (try let th' = rule_mul th in
            let eth,rth = CONJ_PAIR th' in
            let th1,th2 = CONJ_PAIR rth in
            DECOMP_LT (dun,eth::eqs,th1::th2::oths)
        with Failure _ -> try
            let th' = rule_sub th in
            let eth,rth = CONJ_PAIR th' in
            DECOMP_LT (dun,eth::eqs,rth::oths)
        with Failure _ -> DECOMP_LT (th::dun,eqs,oths)) in
  let rec CORE_SPECIAL_ARITH_RULE ths tm =
    if is_conj tm then
      CONJ (CORE_SPECIAL_ARITH_RULE ths (lhand tm))
           (CORE_SPECIAL_ARITH_RULE ths (rand tm))
    else CONTEXT_INT_ARITH ths tm in
  let rec SPECIAL_ARITH_RULE ths tm =
    if is_conj tm then
      CONJ (SPECIAL_ARITH_RULE ths (lhand tm))
           (SPECIAL_ARITH_RULE ths (rand tm))
    else if is_imp tm then
      let atm,btm = dest_imp tm in
      let (aths,eqs) = DECOMP_LT ([],[],[ASSUME atm]) in
      let eth = (SUBS_CONV eqs THENC INT_OF_NUM_CONV) btm in
      let th = CORE_SPECIAL_ARITH_RULE (aths@ths) (rand(concl eth)) in
      DISCH atm (EQ_MP (SYM eth) th)
    else
      let eth = INT_OF_NUM_CONV tm in
      let th = CORE_SPECIAL_ARITH_RULE ths (rand(concl eth)) in
      EQ_MP (SYM eth) th in
  fun (drivers,ariths) ->
    let convs = map (PART_MATCH rand) drivers
    and arule = SPECIAL_ARITH_RULE ariths in
    let match_arith_rule tm =
      tryfind (fun cfn -> let ith = cfn tm in MP ith (arule(lhand(concl ith))))
              convs in
    let rec rule tm =
      if is_conj tm then CONJ (rule(lhand tm)) (rule(rand tm)) else
      let eth =
        (TRY_CONV NONOVERLAP_REVERT_CONV THENC
         BINOP_CONV (LAND_CONV INORMALIZE_RELATIVE_ADDRESS_CONV)) tm in
      EQ_MP (SYM eth) (match_arith_rule(rand(concl eth))) in
    rule;;

let NONOVERLAPPING_TAC gl =
  let thl = map snd (fst gl) and w = snd gl in
  let drivers = NONOVERLAPPING_DRIVERS thl
  and ariths = FILTER_CANONIZE_ASSUMPTIONS thl in
  let th = NONOVERLAPPING_RULE(drivers,ariths) w in
  ACCEPT_TAC th gl;;

(* ------------------------------------------------------------------------- *)
(* Prove orthogonality of components.                                        *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_COMPONENTS_RULE =
  let pth,qth = (CONJ_PAIR o prove)
   (`(nonoverlapping ((a1:N word),l1) (a2,l2)
      ==> orthogonal_components (bytes(a1,l1)) (bytes(a2,l2))) /\
     (orthogonal_components (bytes((a:N word),32)) c
      ==> orthogonal_components (bytes256 a) c) /\
     (orthogonal_components d (bytes(a,32))
      ==> orthogonal_components d (bytes256 a)) /\
     (orthogonal_components (bytes(a,16)) c
      ==> orthogonal_components (bytes128 a) c) /\
     (orthogonal_components d (bytes(a,16))
      ==> orthogonal_components d (bytes128 a)) /\
     (orthogonal_components (bytes(a,8)) c
      ==> orthogonal_components (bytes64 a) c) /\
     (orthogonal_components d (bytes(a,8))
      ==> orthogonal_components d (bytes64 a)) /\
     (orthogonal_components (bytes(a,1)) c
      ==> orthogonal_components (bytes8 a) c) /\
     (orthogonal_components d (bytes(a,1))
      ==> orthogonal_components d (bytes8 a)) /\
     (orthogonal_components (bytes(a,2)) c
      ==> orthogonal_components (bytes16 a) c) /\
     (orthogonal_components d (bytes(a,2))
      ==> orthogonal_components d (bytes16 a)) /\
     (orthogonal_components (bytes(a,4)) c
      ==> orthogonal_components (bytes32 a) c) /\
     (orthogonal_components d (bytes(a,4))
      ==> orthogonal_components d (bytes32 a)) /\
     (orthogonal_components (bytes(a,k)) c
      ==> orthogonal_components (bytelist(a,k)) c) /\
     (orthogonal_components d (bytes(a,k))
      ==> orthogonal_components d (bytelist(a,k)))`,
    CONJ_TAC THENL
     [REWRITE_TAC[NONOVERLAPPING_MODULO; ORTHOGONAL_COMPONENTS_BYTES] THEN
      REWRITE_TAC[WORD_VAL];
      REWRITE_TAC[bytes256; bytes128; bytes64; bytes32; bytes16; bytes8;
                  bytelist; COMPONENT_COMPOSE_ASSOC] THEN
      REWRITE_TAC[ORTHOGONAL_COMPONENTS_SUB_LEFT;
                  ORTHOGONAL_COMPONENTS_SUB_RIGHT]]) in
  let baseconv = PART_MATCH rand pth
  and stepconvs = map (PART_MATCH rand) (CONJUNCTS qth)
  and breakconv = PART_MATCH (rand o rand)
   (REWRITE_RULE[IMP_CONJ] ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT)
  and redconv = BINOP_CONV(LAND_CONV(DEPTH_CONV WORD_NUM_RED_CONV)) in
  (* The terms that NONOVERLAPPING_RULE could not prove.
     This is for logging, and resets whenever ORTHOGONAL_COMPONENTS_RULE is called. *)
  let unproven_nov_terms = ref [] in
  fun cxt ->
    let novrule = fun tm ->
      try
        NONOVERLAPPING_RULE cxt tm
      with f ->
        (if !components_print_log then
          unproven_nov_terms := tm::!unproven_nov_terms);
        raise f
    in
    let mainrule tm =
      let th = baseconv tm in
      let ith = CONV_RULE (LAND_CONV redconv) th in
      let rth = novrule (lhand(concl ith)) in
      MP ith rth in
    let rec midrule tm =
      try let ith = tryfind (fun f -> f tm) stepconvs in
          let rth = midrule(lhand(concl ith)) in
          MP ith rth
      with Failure _ -> mainrule tm in
    let rec toprule tm =
      try let th = breakconv tm in
          let ith = MP th (VALID_COMPONENT_CONV(lhand(concl th))) in
          let rth = toprule(lhand(concl ith)) in
          MP ith rth
      with Failure _ -> midrule tm in
    fun tm -> try ORTHOGONAL_COMPONENTS_CONV tm with Failure _ ->
      unproven_nov_terms := [];
      try toprule tm
      with f ->
        if !components_print_log && !unproven_nov_terms <> [] then
          failwith ("NONOVERLAPPING_RULE: could not prove one of:\n" ^
            (String.concat "\n" (List.map
            (fun tm -> "  * `" ^ (string_of_term tm) ^ "`") !unproven_nov_terms)))
        else raise f;;

let ORTHOGONAL_COMPONENTS_TAC =
  CONV_TAC ORTHOGONAL_COMPONENTS_CONV ORELSE
  (fun gl ->
   let thl = map snd (fst gl) and w = snd gl in
   let drivers = NONOVERLAPPING_DRIVERS thl
   and ariths = FILTER_CANONIZE_ASSUMPTIONS thl in
   let th = ORTHOGONAL_COMPONENTS_RULE(drivers,ariths) w in
   ACCEPT_TAC th gl);;

(* ------------------------------------------------------------------------- *)
(* Convert read c (write d y s) to read c s where c and d are orthogonal.    *)
(* The unpluralized one doesn't use a context and applies at a single level. *)
(* The second one is more general, using a context and applying at depth.    *)
(* ------------------------------------------------------------------------- *)

let COMPONENT_READ_OVER_WRITE_ORTHOGONAL_CONV =
  let pth_orth = prove
   (`orthogonal_components c d ==> read c (write d y s) = read c s`,
    SIMP_TAC[orthogonal_components]) in
  let rule_orth = PART_MATCH (lhand o rand) pth_orth in
  fun tm -> let th = rule_orth tm in
            MP th (ORTHOGONAL_COMPONENTS_CONV(lhand(concl th)));;

let COMPONENTS_READ_OVER_WRITE_ORTHOGONAL_CONV =
  let pth = prove
   (`orthogonal_components c d ==> read c (write d y s) = read c s`,
    SIMP_TAC[orthogonal_components]) in
  let rwconv = PART_MATCH (lhand o rand) pth
  and imprule = MATCH_MP
   (TAUT `(p ==> (q <=> q')) ==> (p ==> q <=> p ==> q')`)
  and conjrule = MATCH_MP
   (TAUT `(p ==> (q <=> q')) ==> (p /\ q <=> p /\ q')`) in
  let singleconv cxt tm =
    let th = rwconv tm in
    MP th (ORTHOGONAL_COMPONENTS_RULE cxt (lhand(concl th))) in
  let rec repconv cxt tm =
    match tm with
      Comb(Comb(Const("read",_),_),
           Comb(Comb(Comb(Const("write",_),_),_),_)) ->
      let th = singleconv cxt tm in
      CONV_RULE (RAND_CONV(repconv cxt)) th
    | _ -> REFL tm in
  fun (drivers,ariths) ->
    let rec conv ths tm =
      match tm with
        Comb(Comb(Const("read",_),_),
             Comb(Comb(Comb(Const("write",_),_),_),_)) ->
          repconv (drivers,ths) tm
      | Abs(x,p) ->
          let x' = genvar(type_of x) in
          let p' = vsubst[x',x] p in
          CONV_RULE (BINOP_CONV(ALPHA_CONV x)) (ABS x' (conv ths p'))
      | Comb(Comb(Const("/\\",_) as op,l),r) ->
         (try let lth = conv ths l in
              try let rth = conv ths r in
                  MK_COMB(AP_TERM op lth,rth)
              with Unchanged -> AP_THM (AP_TERM op lth) r
          with Unchanged ->
              let ths' = ths @
                FILTER_CANONIZE_ASSUMPTIONS(CONJUNCTS(ASSUME l)) in
              let rth = DISCH l (conv ths' r) in
              conjrule rth)
      | Comb(Comb(Const("==>",_) as op,l),r) ->
         (try let lth = conv ths l in
              try let rth = conv ths r in
                  MK_COMB(AP_TERM op lth,rth)
              with Unchanged -> AP_THM (AP_TERM op lth) r
          with Unchanged ->
              let ths' = ths @
                FILTER_CANONIZE_ASSUMPTIONS(CONJUNCTS(ASSUME l)) in
              let rth = DISCH l (conv ths' r) in
              imprule rth)
      | Comb(l,r) ->
         (try let lth = conv ths l in
              try let rth = conv ths r in MK_COMB(lth,rth)
              with Unchanged -> AP_THM lth r
          with Unchanged ->
              AP_TERM l (conv ths r))
      | _ -> raise Unchanged in
  fun tm -> try conv ariths tm with Unchanged -> REFL tm;;

(* ------------------------------------------------------------------------- *)
(* This one attempts to reduce "read c (write d y s)", either by showing     *)
(* c=d or that the two components c and d are orthogonal.                    *)
(* ------------------------------------------------------------------------- *)

let COMPONENT_READ_OVER_WRITE_CONV =
  let pth_same = prove
   (`valid_component c ==> read c (write c y s) = y`,
    SIMP_TAC[valid_component])
  and pth_orth = prove
   (`orthogonal_components c d ==> read c (write d y s) = read c s`,
    SIMP_TAC[orthogonal_components]) in
  let rule_same = PART_MATCH (lhand o rand) pth_same
  and rule_orth = PART_MATCH (lhand o rand) pth_orth
  and orth_rule = ORTHOGONAL_COMPONENTS_RULE(NONOVERLAPPING_DRIVERS[],[]) in
  fun tm ->
   let rule_same_matched, rule_orth_matched = ref false, ref false in
   (try let th = rule_same tm in
        rule_same_matched := true;
        MP th (VALID_COMPONENT_CONV(lhand(concl th)))
    with Failure _ ->
      try let th = rule_orth tm in
          rule_orth_matched := true;
          MP th (orth_rule(lhand(concl th)))
      with Failure _ ->
        (* If tm was of the form `read _ (write _ _ _)`, this failure is from
           *_COMPONENT{S}_CONV which were supposed to prove either fully
           overlapping or orthogonal aliasing relation between the reads and
           writes in tm. This fact might be helpful to the user. *)
        (if !components_print_log && (!rule_same_matched || !rule_orth_matched) then
          Printf.printf
            "Info: could not prove whether the reads and writes of `%s` are fully overlapping or orthogonal.\n"
            (string_of_term tm)
        else ());
        failwith "COMPONENT_READ_OVER_WRITE_CONV");;

(* ------------------------------------------------------------------------- *)
(* Similar tool for "write c y (write c z s)"                                *)
(* ------------------------------------------------------------------------- *)

let COMPONENT_WRITE_OVER_WRITE_CONV =
  let pth = prove
   (`valid_component c ==> write c y (write c z s) = write c y s`,
    SIMP_TAC[valid_component]) in
  let rule = PART_MATCH (lhand o rand) pth in
   fun tm ->
    (let th = rule tm in
     MP th (VALID_COMPONENT_CONV(lhand(concl th))));;

(* ------------------------------------------------------------------------- *)
(* Tactic versions, the latter allowing identical components too.            *)
(* ------------------------------------------------------------------------- *)

let READ_OVER_WRITE_ORTHOGONAL_TAC =
  let tac_orth = (MATCH_MP_TAC o prove)
   (`orthogonal_components c d /\
     read c s' = read c s
     ==> read c (write d y s') = read c s`,
    MESON_TAC[orthogonal_components]) in
  let rec tac g =
   (REFL_TAC ORELSE
    (tac_orth THEN CONJ_TAC THENL [ORTHOGONAL_COMPONENTS_TAC; tac])) g in
  tac;;

let READ_OVER_WRITE_TAC =
  let tac_same = (MATCH_MP_TAC o prove)
   (`valid_component c ==> read c (write c y s) = y`,
    SIMP_TAC[valid_component])
  and tac_orth = (MATCH_MP_TAC o prove)
   (`orthogonal_components c d /\
     read c s' = read c s
     ==> read c (write d y s') = read c s`,
    MESON_TAC[orthogonal_components]) in
  let rec tac g =
   (REFL_TAC ORELSE
    (tac_same THEN CONV_TAC VALID_COMPONENT_CONV) ORELSE
    (tac_orth THEN CONJ_TAC THENL [ORTHOGONAL_COMPONENTS_TAC; tac])) g in
  ASM_REWRITE_TAC[] THEN tac;;

(* ------------------------------------------------------------------------- *)
(* Rule applying a state update theorem of the form                          *)
(* uth |- (write c1 t1) (... (write cn tn) s) = s'                           *)
(* to a theorem involving terms of the form "read d s" and attempting to     *)
(* derive a corresponding theorem with s' replacing s. It fails unless       *)
(* the same theorem is derivable, but also if the original theorem doesn't   *)
(* involve the old state variable s anyway.                                  *)
(* ------------------------------------------------------------------------- *)

let STATE_UPDATE_RULE cxt uth th =
  let utm,s' = dest_eq(concl uth)
  and tm = concl th in
  let s = repeat rand utm in
  if not(vfree_in s tm) then failwith "STATE_UPDATE_RULE" else
  let th0 = SUBS_CONV[uth] (vsubst[utm,s] (concl th)) in
  let th1 = CONV_RULE(LAND_CONV
    (COMPONENTS_READ_OVER_WRITE_ORTHOGONAL_CONV cxt)) th0 in
  EQ_MP th1 th;;

(* ------------------------------------------------------------------------- *)
(* Create conjunction of newly arising clauses for state update.             *)
(* ------------------------------------------------------------------------- *)

let STATE_UPDATE_NEW_RULE th =
  let rec getwrites tm =
    match tm with
      Comb(Comb(Comb(Const("write",_),c),y),t) ->
        c::getwrites t
    | _ -> [] in
  let ccs = getwrites(lhand(concl th)) in
  let mk_new_rule c =
    let th' = SYM(AP_TERM (list_mk_icomb "read" [c]) th) in
    CONV_RULE(RAND_CONV(REPEATC COMPONENT_READ_OVER_WRITE_CONV)) th' in
  map mk_new_rule ccs;;

(* ------------------------------------------------------------------------- *)
(* Produce updated versions of existing assumptions                          *)
(* Works from antecedent in the goal, which is retained after its use.       *)
(* ------------------------------------------------------------------------- *)

let ASSUMPTION_STATE_UPDATE_TAC =
  let rec memorable tm =
    match tm with
      Var(_,_) -> false
    | Abs(_,b) -> memorable b
    | Const(n,_) -> n = "memory"
    | Comb(s,t) -> memorable s || memorable t in
  fun gl -> (DISCH_THEN(fun uth ->
   let utm = lhand(concl uth)
   and thl = map snd (fst gl) in
   let s = repeat rand utm in
   let newthms =
     if memorable utm then
       let thy,thn = partition (vfree_in s o concl) thl in
       let cxt = (NONOVERLAPPING_DRIVERS thn,FILTER_CANONIZE_ASSUMPTIONS thn) in
       mapfilter (fun thi ->
          try
            STATE_UPDATE_RULE cxt uth thi
          with Failure failmsg ->
            (if !components_print_log &&
                starts_with "NONOVERLAPPING_RULE" failmsg then
              (Printf.printf "Info: assumption `%s` is erased.\n"  (string_of_term (concl thi));
               Printf.printf "- Reason: %s\n" failmsg));
            failwith failmsg) thy
     else
       let thy = filter (vfree_in s o concl) thl in
       mapfilter (STATE_UPDATE_RULE ([],[]) uth) thy in
   MP_TAC uth THEN MAP_EVERY ASSUME_TAC newthms)) gl;;

(* ------------------------------------------------------------------------- *)
(* Rule for "non-selfmodification" when supplied with std exec theorem       *)
(* Works from antecedent in the goal, which is retained after its use.       *)
(* ------------------------------------------------------------------------- *)

let NONSELFMODIFYING_STATE_UPDATE_TAC bth =
  DISCH_THEN(fun th ->
    (if not (is_eq (concl th)) then failwith
      ("NONSELFMODIFYING_STATE_UPDATE_TAC: the goal must have " ^
       "`write ... = ... ==> ...` as conclusion, but got `" ^
       (string_of_term (concl th)) ^ " ==> ...`") else ());
    MP_TAC th THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (lhand (concl th)) o MATCH_MP bth) THEN
    ANTS_TAC THENL
     [READ_OVER_WRITE_ORTHOGONAL_TAC ORELSE
      FAIL_TAC "could not prove that updates will not modify the program code";
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th] THEN
      DISCH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Apply conversion at depth only within a component itself (designed        *)
(* for normalizing addresses of loads and stores, leaving the data).         *)
(* ------------------------------------------------------------------------- *)

let rec SUB_COMPONENTS_CONV conv tm =
  match tm with
  | Comb(Const("write",_),_) -> RAND_CONV conv tm
  | Comb(Const("read",_),_) -> RAND_CONV conv tm
  | Comb(l,r) -> COMB_CONV (SUB_COMPONENTS_CONV conv) tm
  | Abs(x,bod) -> ABS_CONV (SUB_COMPONENTS_CONV conv) tm
  | _ -> REFL tm;;
