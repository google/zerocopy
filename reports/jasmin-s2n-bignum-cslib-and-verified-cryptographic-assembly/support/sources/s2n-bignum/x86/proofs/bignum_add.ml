(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addition of bignums.                                                      *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_add.o";;
 ****)

let bignum_add_mc =
  define_assert_from_elf "bignum_add_mc" "x86/generic/bignum_add.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x48; 0x39; 0xd7;        (* CMP (% rdi) (% rdx) *)
  0x48; 0x0f; 0x42; 0xd7;  (* CMOVB (% rdx) (% rdi) *)
  0x4c; 0x39; 0xc7;        (* CMP (% rdi) (% r8) *)
  0x4c; 0x0f; 0x42; 0xc7;  (* CMOVB (% r8) (% rdi) *)
  0x4c; 0x39; 0xc2;        (* CMP (% rdx) (% r8) *)
  0x72; 0x47;              (* JB (Imm8 (word 71)) *)
  0x48; 0x29; 0xd7;        (* SUB (% rdi) (% rdx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x48; 0xff; 0xc2;        (* INC (% rdx) *)
  0x4d; 0x85; 0xc0;        (* TEST (% r8) (% r8) *)
  0x74; 0x25;              (* JE (Imm8 (word 37)) *)
  0x4a; 0x8b; 0x04; 0xd1;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,r10))) *)
  0x4b; 0x13; 0x04; 0xd1;  (* ADC (% rax) (Memop Quadword (%%% (r9,3,r10))) *)
  0x4a; 0x89; 0x04; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% rax) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x49; 0xff; 0xc8;        (* DEC (% r8) *)
  0x75; 0xec;              (* JNE (Imm8 (word 236)) *)
  0xeb; 0x0f;              (* JMP (Imm8 (word 15)) *)
  0x4a; 0x8b; 0x04; 0xd1;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,r10))) *)
  0x48; 0x83; 0xd0; 0x00;  (* ADC (% rax) (Imm8 (word 0)) *)
  0x4a; 0x89; 0x04; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% rax) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x48; 0xff; 0xca;        (* DEC (% rdx) *)
  0x75; 0xec;              (* JNE (Imm8 (word 236)) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x83; 0xd0; 0x00;  (* ADC (% rax) (Imm8 (word 0)) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x75; 0x43;              (* JNE (Imm8 (word 67)) *)
  0xc3;                    (* RET *)
  0x4c; 0x29; 0xc7;        (* SUB (% rdi) (% r8) *)
  0x49; 0x29; 0xd0;        (* SUB (% r8) (% rdx) *)
  0x48; 0x85; 0xd2;        (* TEST (% rdx) (% rdx) *)
  0x74; 0x14;              (* JE (Imm8 (word 20)) *)
  0x4a; 0x8b; 0x04; 0xd1;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,r10))) *)
  0x4b; 0x13; 0x04; 0xd1;  (* ADC (% rax) (Memop Quadword (%%% (r9,3,r10))) *)
  0x4a; 0x89; 0x04; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% rax) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x48; 0xff; 0xca;        (* DEC (% rdx) *)
  0x75; 0xec;              (* JNE (Imm8 (word 236)) *)
  0x4b; 0x8b; 0x04; 0xd1;  (* MOV (% rax) (Memop Quadword (%%% (r9,3,r10))) *)
  0x48; 0x83; 0xd0; 0x00;  (* ADC (% rax) (Imm8 (word 0)) *)
  0x4a; 0x89; 0x04; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% rax) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x49; 0xff; 0xc8;        (* DEC (% r8) *)
  0x75; 0xec;              (* JNE (Imm8 (word 236)) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x83; 0xd0; 0x00;  (* ADC (% rax) (Imm8 (word 0)) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x75; 0x01;              (* JNE (Imm8 (word 1)) *)
  0xc3;                    (* RET *)
  0x4a; 0x89; 0x04; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% rax) *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0xeb; 0x04;              (* JMP (Imm8 (word 4)) *)
  0x4a; 0x89; 0x04; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% rax) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x48; 0xff; 0xcf;        (* DEC (% rdi) *)
  0x75; 0xf4;              (* JNE (Imm8 (word 244)) *)
  0xc3                     (* RET *)
];;

let bignum_add_tmc = define_trimmed "bignum_add_tmc" bignum_add_mc;;

let BIGNUM_ADD_EXEC = X86_MK_EXEC_RULE bignum_add_tmc;;

(* ------------------------------------------------------------------------- *)
(* Common tactic for slightly different standard and Windows variants.       *)
(* ------------------------------------------------------------------------- *)

let tac execth cleanpost offset =
  W64_GEN_TAC `p:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `m:num` THEN MAP_EVERY X_GEN_TAC [`x:int64`; `a:num`] THEN
  W64_GEN_TAC `n:num` THEN MAP_EVERY X_GEN_TAC [`y:int64`; `b:num`] THEN
  X_GEN_TAC `pc:num` THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN DISCH_TAC THEN

  (*** Remove redundancy in the conclusion ***)

  ENSURES_POSTCONDITION_TAC cleanpost THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[lowdigits; MOD_LT] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP (64 * p)`) THEN
    SIMP_TAC[MOD_MULT_ADD; MOD_LT; BIGNUM_FROM_MEMORY_BOUND] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Reshuffle to handle clamping and just assume m <= p and n <= p ***)

  ENSURES_SEQUENCE_TAC (offset 0x11)
   `\s. read RDI s = word p /\
        read RSI s = z /\
        read RDX s = word(MIN m p) /\
        read RCX s = x /\
        read R8 s = word(MIN n p) /\
        read R9 s = y /\
        read R10 s = word 0 /\
        bignum_from_memory(x,MIN m p) s = lowdigits a p /\
        bignum_from_memory(y,MIN n p) s = lowdigits b p` THEN
  CONJ_TAC THENL
   [X86_SIM_TAC execth (1--5) THEN
    ASM_REWRITE_TAC[lowdigits; REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
        (GSYM BIGNUM_FROM_MEMORY_MOD)] THEN
    GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV) [GSYM COND_RAND] THEN
    CONJ_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC)] THEN
  SUBGOAL_THEN
   `lowdigits (a + b) p = lowdigits (lowdigits a p + lowdigits b p) p`
  SUBST1_TAC THENL
   [REWRITE_TAC[lowdigits] THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w n. w = z \/
          nonoverlapping_modulo (2 EXP 64) (val w,8 * n) (val z,8 * p)
          ==> w:int64 = z \/
              nonoverlapping_modulo (2 EXP 64)
                 (val w,8 * MIN n p) (val z,8 * p)`
   (fun th -> DISCH_THEN(CONJUNCTS_THEN(MP_TAC o MATCH_MP th)))
  THENL
   [POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC MONO_OR THEN REWRITE_TAC[] THEN
    DISCH_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`p < 2 EXP 64`; `val(word p:int64) = p`] THEN
  SUBGOAL_THEN `MIN m p < 2 EXP 64 /\ MIN n p < 2 EXP 64` MP_TAC THENL
   [ASM_ARITH_TAC; POP_ASSUM_LIST(K ALL_TAC)] THEN
  MP_TAC(ARITH_RULE `MIN m p <= p /\ MIN n p <= p`) THEN
  MAP_EVERY SPEC_TAC
   [`lowdigits a p`,`a:num`; `lowdigits b p`,`b:num`;
    `MIN m p`,`m:num`; `MIN n p`,`n:num`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN REPEAT DISCH_TAC THEN
  MAP_EVERY VAL_INT64_TAC [`m:num`; `n:num`] THEN
  BIGNUM_RANGE_TAC "m" "a" THEN BIGNUM_RANGE_TAC "n" "b" THEN

  (*** Get a basic bound on p from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Case split following the initial branch, m >= n case then m < n ***)

  ASM_CASES_TAC `n:num <= m` THENL
   [SUBGOAL_THEN `~(m:num < n)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NOT_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `b < 2 EXP (64 * m)` ASSUME_TAC THENL
     [TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN
      ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL];
      ALL_TAC] THEN

    ENSURES_SEQUENCE_TAC (offset 0x49)
     `\s. read RDI s = word(p - m) /\
          read RSI s = z /\
          read RDX s = word(m - n + 1) /\
          read RCX s = x /\
          read R9 s = y /\
          read R10 s = word n /\
          bignum_from_memory (word_add x (word(8 * n)),m - n) s =
          highdigits a n /\
          2 EXP (64 * n) * bitval(read CF s) + bignum_from_memory(z,n) s =
          lowdigits a n + lowdigits b n` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `n = 0` THENL
       [UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN
        ASM_REWRITE_TAC[SUB_0] THEN X86_SIM_TAC execth (1--7) THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ASM_REWRITE_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE;
        ALL_TAC] THEN
      ENSURES_WHILE_PUP_TAC `n:num` (offset 0x24) (offset 0x36)
       `\i s. (read RDI s = word(p - m) /\
               read RSI s = z /\
               read RDX s = word(m - n + 1) /\
               read RCX s = x /\
               read R9 s = y /\
               read R8 s = word(n - i) /\
               read R10 s = word i /\
               bignum_from_memory (word_add x (word(8 * i)),m - i) s =
               highdigits a i /\
               bignum_from_memory (word_add y (word(8 * i)),n - i) s =
               highdigits b i /\
               2 EXP (64 * i) * bitval(read CF s) + bignum_from_memory(z,i) s =
               lowdigits a i + lowdigits b i) /\
              (read ZF s <=> i = n)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUB_0] THEN X86_SIM_TAC execth (1--7) THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ASM_REWRITE_TAC[WORD_ADD; WORD_SUB];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        ASM_REWRITE_TAC[] THEN X86_SIM_TAC execth [1];
        X86_SIM_TAC execth (1--2)] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      SUBGOAL_THEN `i:num < m` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `i:num` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN ENSURES_INIT_TAC "s0" THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [ONCE_REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
       BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS])) THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN STRIP_TAC THEN STRIP_TAC THEN
      X86_STEPS_TAC execth (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[ARITH_RULE `n - (i + 1) = n - i - 1`] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < n ==> 1 <= n - i`];
        DISCH_THEN SUBST1_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < n ==> (i + 1 = n <=> n - i - 1 = 0)`] THEN
      CONJ_TAC THENL
       [ALL_TAC; VAL_INT64_TAC `n - i - 1` THEN ASM_REWRITE_TAC[]] THEN
      REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
      REWRITE_TAC[GSYM ACCUMULATE_ADC; ARITH_RULE
       `(t * e) * x + z + t * y:num = t * (e * x + y) + z`] THEN
      ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; VAL_WORD_BITVAL] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES] THEN ARITH_TAC;
      ALL_TAC] THEN

    ENSURES_SEQUENCE_TAC (offset 0x57)
     `\s. read RDI s = word(p - m) /\
          read RSI s = z /\
          read R10 s = word m /\
          2 EXP (64 * m) * val(read RAX s) + bignum_from_memory(z,m) s =
          lowdigits a m + lowdigits b m` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `m:num = n` THENL
       [UNDISCH_THEN `m:num = n` SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
        GHOST_INTRO_TAC `cin:bool` `read CF` THEN
        X86_SIM_TAC execth (1--4) THEN
        ASM_REWRITE_TAC[VAL_WORD_BITVAL];
        ALL_TAC] THEN
      SUBGOAL_THEN `n < m /\ 0 < m - n /\ ~(m - n = 0)` STRIP_ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `m - n:num` THEN
      ENSURES_WHILE_PUP_TAC `m - n:num` (offset 0x3a) (offset 0x4c)
       `\i s. (read RDI s = word(p - m) /\
               read RSI s = z /\
               read RCX s = x /\
               read RDX s = word(m - n - i) /\
               read R10 s = word(n + i) /\
               bignum_from_memory(word_add x (word(8 * (n + i))),
                                  m - (n + i)) s =
               highdigits a (n + i) /\
               2 EXP (64 * (n + i)) * bitval(read CF s) +
               bignum_from_memory(z,n + i) s =
               lowdigits a (n + i) + lowdigits b (n + i)) /\
              (read ZF s <=> i = m - n)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUB_0] THEN X86_SIM_TAC execth (1--2) THEN
        ASM_REWRITE_TAC[ADD_CLAUSES] THEN
        REWRITE_TAC[VAL_EQ; WORD_RULE
         `word(a + 1):int64 = word 1 <=> word a:int64 = word 0`] THEN
        CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_RULE] THEN
        ASM_REWRITE_TAC[GSYM VAL_EQ_0];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        ASM_REWRITE_TAC[] THEN X86_SIM_TAC execth [1];
        ASM_SIMP_TAC[ARITH_RULE `n:num <= m ==> n + m - n = m`] THEN
        GHOST_INTRO_TAC `cin:bool` `read CF` THEN
        X86_SIM_TAC execth (1--3) THEN
        ASM_REWRITE_TAC[VAL_WORD_BITVAL]] THEN
      ASM_SIMP_TAC[ARITH_RULE
       `n:num < m
        ==> (i < m - n <=> n + i < m) /\ (i = m - n <=> n + i = m)`] THEN
      REWRITE_TAC[ARITH_RULE `m - n - i:num = m - (n + i)`] THEN
      REWRITE_TAC[ARITH_RULE `n + i + 1 = (n + i) + 1`] THEN
      X_GEN_TAC `j:num` THEN MP_TAC(ARITH_RULE `n <= n + j`) THEN
      SPEC_TAC(`n + j:num`,`i:num`) THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      VAL_INT64_TAC `i:num` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN ENSURES_INIT_TAC "s0" THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [ONCE_REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
       BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS]) THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN STRIP_TAC THEN
      X86_STEPS_TAC execth (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[ARITH_RULE `n - (i + 1) = n - i - 1`] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < n ==> 1 <= n - i`];
        DISCH_THEN SUBST1_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < n ==> (i + 1 = n <=> n - i - 1 = 0)`] THEN
      CONJ_TAC THENL
       [ALL_TAC; VAL_INT64_TAC `m - i - 1` THEN ASM_REWRITE_TAC[]] THEN
      REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
      REWRITE_TAC[GSYM ACCUMULATE_ADC_0; ADD_CLAUSES; ARITH_RULE
       `(t * e) * x + z + t * y:num = t * (e * x + y) + z`] THEN
      ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; VAL_WORD_BITVAL] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
      MATCH_MP_TAC(NUM_RING `b = 0 ==> x = e * b + x`) THEN
      MATCH_MP_TAC BIGDIGIT_ZERO THEN TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN
      ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL];
      ALL_TAC] THEN

    ASM_CASES_TAC `m:num = p` THENL
     [UNDISCH_THEN `m:num = p` SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
      X86_SIM_TAC execth (1--2) THEN ASM_REWRITE_TAC[] THEN
      BINOP_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `0 < p - m /\ ~(p - m = 0)` STRIP_ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    VAL_INT64_TAC `p - m:num` THEN
    ENSURES_SEQUENCE_TAC (offset 0xac)
     `\s. read RDI s = word(p - m) /\
          read RSI s = z /\
          read R10 s = word m /\
          read RAX s = word 0 /\
          bignum_from_memory(z,m + 1) s = a + b` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN ASM_REWRITE_TAC[] THEN
      GHOST_INTRO_TAC `d:int64` `read RAX` THEN
      X86_SIM_TAC execth (1--5) THEN
      GEN_REWRITE_TAC LAND_CONV [ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
      BINOP_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `p = m + 1` THENL
     [UNDISCH_THEN `p = m + 1` SUBST_ALL_TAC THEN REWRITE_TAC[ADD_SUB2] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_SUB2]) THEN
      X86_SIM_TAC execth (1--3) THEN
      REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `0 < p - (m + 1) /\ ~(p - (m + 1) = 0) /\ ~(p - m = 1) /\ m + 1 <= p`
    STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ENSURES_WHILE_PUP_TAC `p - (m + 1):num` (offset 0xa8) (offset 0xb2)
     `\i s. (read RDI s = word(p - (m + 1) - i) /\
             read R10 s = word((m + 1) + i) /\
             read RSI s = z /\
             read RAX s = word 0 /\
             bignum_from_memory(z,(m + 1) + i) s = a + b) /\
            (read ZF s <=> i = p - (m + 1))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUB_0] THEN X86_SIM_TAC execth (1--3) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; VAL_WORD_1] THEN
      CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_RULE] THEN
      REWRITE_TAC[ARITH_RULE `p - (m + 1) = p - m - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
      ALL_TAC; (*** Main loop invariant ***)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      X86_SIM_TAC execth [1];
      ASM_SIMP_TAC[ARITH_RULE `0 < m - n ==> n + m - n = m`] THEN
      X86_SIM_TAC execth [1] THEN
      REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES]] THEN
    X_GEN_TAC `j:num` THEN MP_TAC(ARITH_RULE `m + 1 <= (m + 1) + j`) THEN
    REWRITE_TAC[ARITH_RULE
     `p - (m + 1) - (j + 1) = p - ((m + 1) + (j + 1))`] THEN
    REWRITE_TAC[ARITH_RULE `p - (m + 1) - j = p - ((m + 1) + j)`] THEN
    REWRITE_TAC[ARITH_RULE `(m + 1) + (j + 1) = ((m + 1) + j) + 1`] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `0 < p - (m + 1)
      ==> (j + 1 = p - (m + 1) <=> ((m + 1) + j) + 1 = p) /\
          (j < p - (m + 1) <=> (m + 1) + j < p) /\
          (j = p - (m + 1) <=> (m + 1) + j = p)`] THEN
    SPEC_TAC(`(m + 1) + j:num`,`i:num`) THEN REPEAT STRIP_TAC THEN
    VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    X86_SIM_TAC execth (1--3) THEN
    REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `p - (i + 1) = p - i - 1`] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < n ==> 1 <= n - i`];
      DISCH_THEN SUBST1_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < p ==> (i + 1 = p <=> p - i = 1)`] THEN
    REWRITE_TAC[VAL_EQ] THEN MATCH_MP_TAC WORD_EQ_IMP THEN
    REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;

    (**** The other branch, very similar mutatis mutandis ***)

    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
    SUBGOAL_THEN `m:num <= n` ASSUME_TAC THENL
     [ASM_SIMP_TAC[LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `a < 2 EXP (64 * n)` ASSUME_TAC THENL
     [TRANS_TAC LTE_TRANS `2 EXP (64 * m)` THEN
      ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL];
      ALL_TAC] THEN

    ENSURES_SEQUENCE_TAC (offset 0x7c)
     `\s. read RDI s = word(p - n) /\
          read RSI s = z /\
          read R8 s = word(n - m) /\
          read R9 s = y /\
          read RCX s = x /\
          read R10 s = word m /\
          bignum_from_memory (word_add y (word(8 * m)),n - m) s =
          highdigits b m /\
          2 EXP (64 * m) * bitval(read CF s) + bignum_from_memory(z,m) s =
          lowdigits a m + lowdigits b m` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `m = 0` THENL
       [UNDISCH_THEN `m = 0` SUBST_ALL_TAC THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
        X86_SIM_TAC execth (1--6) THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ASM_REWRITE_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE;
        ALL_TAC] THEN
      ENSURES_WHILE_PUP_TAC `m:num` (offset 0x68) (offset 0x7a)
       `\i s. (read RDI s = word(p - n) /\
               read RSI s = z /\
               read R8 s = word(n - m) /\
               read R9 s = y /\
               read RCX s = x /\
               read RDX s = word(m - i) /\
               read R10 s = word i /\
               bignum_from_memory (word_add y (word(8 * i)),n - i) s =
               highdigits b i /\
               bignum_from_memory (word_add x (word(8 * i)),m - i) s =
               highdigits a i /\
               2 EXP (64 * i) * bitval(read CF s) + bignum_from_memory(z,i) s =
               lowdigits a i + lowdigits b i) /\
              (read ZF s <=> i = m)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUB_0] THEN X86_SIM_TAC execth (1--6) THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ASM_REWRITE_TAC[WORD_ADD; WORD_SUB];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        X86_SIM_TAC execth [1];
        X86_SIM_TAC execth [1]] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      SUBGOAL_THEN `i:num < n` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `i:num` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN ENSURES_INIT_TAC "s0" THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [ONCE_REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
       BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS])) THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN STRIP_TAC THEN STRIP_TAC THEN
      X86_STEPS_TAC execth (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[ARITH_RULE `m - (i + 1) = m - i - 1`] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < m ==> 1 <= m - i`];
        DISCH_THEN SUBST1_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < m ==> (i + 1 = m <=> m - i - 1 = 0)`] THEN
      CONJ_TAC THENL
       [ALL_TAC; VAL_INT64_TAC `m - i - 1` THEN ASM_REWRITE_TAC[]] THEN
      REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
      REWRITE_TAC[GSYM ACCUMULATE_ADC; ARITH_RULE
       `(t * e) * y + z + t * x:num = t * (e * y + x) + z`] THEN
      ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; VAL_WORD_BITVAL] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES] THEN ARITH_TAC;
      ALL_TAC] THEN

    ENSURES_SEQUENCE_TAC (offset 0x99)
     `\s. read RDI s = word(p - n) /\
          read RSI s = z /\
          read R10 s = word n /\
          2 EXP (64 * n) * val(read RAX s) + bignum_from_memory(z,n) s =
          lowdigits a n + lowdigits b n` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `~(m = n) /\ 0 < n - m /\ ~(n - m = 0)`
      STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `n - m:num` THEN
      ENSURES_WHILE_PUP_TAC `n - m:num` (offset 0x7c) (offset 0x8e)
       `\i s. (read RDI s = word(p - n) /\
               read RSI s = z /\
               read R9 s = y /\
               read R8 s = word(n - m - i) /\
               read R10 s = word(m + i) /\
               bignum_from_memory(word_add y (word(8 * (m + i))),
                                  n - (m + i)) s =
               highdigits b (m + i) /\
               2 EXP (64 * (m + i)) * bitval(read CF s) +
               bignum_from_memory(z,m + i) s =
               lowdigits a (m + i) + lowdigits b (m + i)) /\
              (read ZF s <=> i = n - m)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
        ENSURES_INIT_TAC "s0" THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
        ASM_REWRITE_TAC[WORD_RULE `word_sub (word(m + 1)) (word 1) = word m`];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        ASM_REWRITE_TAC[] THEN X86_SIM_TAC execth [1];
        ASM_SIMP_TAC[ARITH_RULE `m:num <= n ==> m + n - m = n`] THEN
        GHOST_INTRO_TAC `cin:bool` `read CF` THEN ASM_REWRITE_TAC[] THEN
        X86_SIM_TAC execth (1--3) THEN
        ASM_REWRITE_TAC[VAL_WORD_BITVAL]] THEN
      ASM_SIMP_TAC[ARITH_RULE
       `m:num < n
        ==> (i < n - m <=> m + i < n) /\ (i = n - m <=> m + i = n)`] THEN
      REWRITE_TAC[ARITH_RULE `n - m - i:num = n - (m + i)`] THEN
      REWRITE_TAC[ARITH_RULE `m + i + 1 = (m + i) + 1`] THEN
      X_GEN_TAC `j:num` THEN MP_TAC(ARITH_RULE `m <= m + j`) THEN
      SPEC_TAC(`m + j:num`,`i:num`) THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      VAL_INT64_TAC `i:num` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN ENSURES_INIT_TAC "s0" THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [ONCE_REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
       BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS]) THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN STRIP_TAC THEN
      X86_STEPS_TAC execth (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[ARITH_RULE `m - (i + 1) = m - i - 1`] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < m ==> 1 <= m - i`];
        DISCH_THEN SUBST1_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < m ==> (i + 1 = m <=> m - i - 1 = 0)`] THEN
      CONJ_TAC THENL
       [ALL_TAC; VAL_INT64_TAC `n - i - 1` THEN ASM_REWRITE_TAC[]] THEN
      REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
      REWRITE_TAC[GSYM ACCUMULATE_ADC_0; ADD_CLAUSES; ARITH_RULE
       `(t * e) * y + z + t * x:num = t * (e * y + x) + z`] THEN
      ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; VAL_WORD_BITVAL] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
      MATCH_MP_TAC(NUM_RING `a = 0 ==> x + y + z = e * a + y + x + z`) THEN
      MATCH_MP_TAC BIGDIGIT_ZERO THEN TRANS_TAC LTE_TRANS `2 EXP (64 * m)` THEN
      ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL];
      ALL_TAC] THEN

    ASM_CASES_TAC `n:num = p` THENL
     [UNDISCH_THEN `n:num = p` SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
      X86_SIM_TAC execth (1--2) THEN
      BINOP_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `0 < p - n /\ ~(p - n = 0)` STRIP_ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    VAL_INT64_TAC `p - n:num` THEN
    ENSURES_SEQUENCE_TAC (offset 0xac)
     `\s. read RDI s = word(p - n) /\
          read RSI s = z /\
          read R10 s = word n /\
          read RAX s = word 0 /\
          bignum_from_memory(z,n + 1) s = a + b` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN ASM_REWRITE_TAC[] THEN
      GHOST_INTRO_TAC `d:int64` `read RAX` THEN
      X86_SIM_TAC execth (1--5) THEN
      GEN_REWRITE_TAC LAND_CONV [ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
      BINOP_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `p = n + 1` THENL
     [UNDISCH_THEN `p = n + 1` SUBST_ALL_TAC THEN REWRITE_TAC[ADD_SUB2] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_SUB2]) THEN
      X86_SIM_TAC execth (1--3) THEN
      REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `0 < p - (n + 1) /\ ~(p - (n + 1) = 0) /\ ~(p - n = 1) /\ n + 1 <= p`
    STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ENSURES_WHILE_PUP_TAC `p - (n + 1):num` (offset 0xa8) (offset 0xb2)
     `\i s. (read RDI s = word(p - (n + 1) - i) /\
             read R10 s = word((n + 1) + i) /\
             read RSI s = z /\
             read RAX s = word 0 /\
             bignum_from_memory(z,(n + 1) + i) s = a + b) /\
            (read ZF s <=> i = p - (n + 1))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUB_0] THEN
      X86_SIM_TAC execth (1--3) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; VAL_WORD_1] THEN
      ASM_REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM VAL_EQ_1] THEN
      CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_RULE] THEN
      REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
      ALL_TAC; (*** Main loop invariant ***)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ASM_REWRITE_TAC[] THEN X86_SIM_TAC execth [1];
      ASM_SIMP_TAC[ARITH_RULE `0 < n - m ==> m + n - m = n`] THEN
      X86_SIM_TAC execth [1] THEN
      REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES]] THEN
    X_GEN_TAC `j:num` THEN MP_TAC(ARITH_RULE `n + 1 <= (n + 1) + j`) THEN
    REWRITE_TAC[ARITH_RULE
     `p - (n + 1) - (j + 1) = p - ((n + 1) + (j + 1))`] THEN
    REWRITE_TAC[ARITH_RULE `p - (n + 1) - j = p - ((n + 1) + j)`] THEN
    REWRITE_TAC[ARITH_RULE `(n + 1) + (j + 1) = ((n + 1) + j) + 1`] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `0 < p - (n + 1)
      ==> (j + 1 = p - (n + 1) <=> ((n + 1) + j) + 1 = p) /\
          (j < p - (n + 1) <=> (n + 1) + j < p) /\
          (j = p - (n + 1) <=> (n + 1) + j = p)`] THEN
    SPEC_TAC(`(n + 1) + j:num`,`i:num`) THEN REPEAT STRIP_TAC THEN
    VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    X86_SIM_TAC execth (1--3) THEN
    REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `p - (i + 1) = p - i - 1`] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < m ==> 1 <= m - i`];
      DISCH_THEN SUBST1_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < p ==> (i + 1 = p <=> p - i = 1)`] THEN
    REWRITE_TAC[VAL_EQ] THEN MATCH_MP_TAC WORD_EQ_IMP THEN
    REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness of standard ABI version.                                      *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_ADD_CORRECT = prove
 (`!p z m x a n y b pc.
        nonoverlapping (word pc,0xb5) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val m) (z,8 * val p)) /\
        (y = z \/ nonoverlapping(y,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_add_tmc /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [p;z;m;x;n;y] s /\
                  bignum_from_memory (x,val m) s = a /\
                  bignum_from_memory (y,val n) s = b)
             (\s. (read RIP s = word(pc + 0x5c) \/
                   read RIP s = word(pc + 0x9e) \/
                   read RIP s = word(pc + 0xb4)) /\
                  bignum_from_memory (z,val p) s =
                  (a + b) MOD 2 EXP (64 * val p) /\
                  2 EXP (64 * val p) * val(C_RETURN s) +
                  bignum_from_memory (z,val p) s =
                  lowdigits a (val p) + lowdigits b (val p))
             (MAYCHANGE [RIP; RAX; RDI; RDX; R8; R10] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  tac BIGNUM_ADD_EXEC
   `\s. (read RIP s = word(pc + 0x5c) \/
         read RIP s = word(pc + 0x9e) \/
         read RIP s = word(pc + 0xb4)) /\
        2 EXP (64 * p) * val(read RAX s) +
        bignum_from_memory (z,p) s = lowdigits a p + lowdigits b p`
   (curry mk_comb `(+) (pc:num)` o mk_small_numeral));;

let BIGNUM_ADD_NOIBT_SUBROUTINE_CORRECT = prove
 (`!p z m x a n y b pc stackpointer returnaddress.
      ALL (nonoverlapping (z,8 * val p)) [(word pc,LENGTH bignum_add_tmc); (stackpointer,8)] /\
      (x = z \/ nonoverlapping(x,8 * val m) (z,8 * val p)) /\
      (y = z \/ nonoverlapping(y,8 * val n) (z,8 * val p))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_add_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [p;z;m;x;n;y] s /\
                bignum_from_memory (x,val m) s = a /\
                bignum_from_memory (y,val n) s = b)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,val p) s =
                (a + b) MOD 2 EXP (64 * val p) /\
                2 EXP (64 * val p) * val(C_RETURN s) +
                bignum_from_memory (z,val p) s =
                lowdigits a (val p) + lowdigits b (val p))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bignum(z,val p)])`,
  X86_ADD_RETURN_NOSTACK_TAC BIGNUM_ADD_EXEC BIGNUM_ADD_CORRECT);;

let BIGNUM_ADD_SUBROUTINE_CORRECT = prove
 (`!p z m x a n y b pc stackpointer returnaddress.
      ALL (nonoverlapping (z,8 * val p)) [(word pc,LENGTH bignum_add_mc); (stackpointer,8)] /\
      (x = z \/ nonoverlapping(x,8 * val m) (z,8 * val p)) /\
      (y = z \/ nonoverlapping(y,8 * val n) (z,8 * val p))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_add_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [p;z;m;x;n;y] s /\
                bignum_from_memory (x,val m) s = a /\
                bignum_from_memory (y,val n) s = b)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,val p) s =
                (a + b) MOD 2 EXP (64 * val p) /\
                2 EXP (64 * val p) * val(C_RETURN s) +
                bignum_from_memory (z,val p) s =
                lowdigits a (val p) + lowdigits b (val p))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bignum(z,val p)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_ADD_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_add_windows_mc = define_from_elf
   "bignum_add_windows_mc" "x86/generic/bignum_add.obj";;

let bignum_add_windows_tmc = define_trimmed "bignum_add_windows_tmc" bignum_add_windows_mc;;

let BIGNUM_ADD_WINDOWS_CORRECT = prove
 (`!p z m x a n y b pc.
        nonoverlapping (word pc,0xd3) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val m) (z,8 * val p)) /\
        (y = z \/ nonoverlapping(y,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_add_windows_tmc /\
                  read RIP s = word(pc + 0x18) /\
                  C_ARGUMENTS [p;z;m;x;n;y] s /\
                  bignum_from_memory (x,val m) s = a /\
                  bignum_from_memory (y,val n) s = b)
             (\s. (read RIP s = word(pc + 0x74) \/
                   read RIP s = word(pc + 0xb8) \/
                   read RIP s = word(pc + 0xd0)) /\
                  bignum_from_memory (z,val p) s =
                  (a + b) MOD 2 EXP (64 * val p) /\
                  2 EXP (64 * val p) * val(C_RETURN s) +
                  bignum_from_memory (z,val p) s =
                  lowdigits a (val p) + lowdigits b (val p))
             (MAYCHANGE [RIP; RAX; RDI; RDX; R8; R10] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  tac (X86_MK_EXEC_RULE bignum_add_windows_tmc)
   `\s. (read RIP s = word(pc + 0x74) \/
         read RIP s = word(pc + 0xb8) \/
         read RIP s = word(pc + 0xd0)) /\
        2 EXP (64 * p) * val(read RAX s) +
        bignum_from_memory (z,p) s = lowdigits a p + lowdigits b p`
   (curry mk_comb `(+) (pc:num)` o mk_small_numeral o
    (fun n -> if n < 0x5c then n + 24
              else if n < 0x9e then n + 26
              else n + 28)));;

let BIGNUM_ADD_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!p z m x a n y b pc stackpointer returnaddress.
      ALL (nonoverlapping (word_sub stackpointer (word 16),16))
          [(word pc,LENGTH bignum_add_windows_tmc); (x,8 * val m); (y,8 * val n)] /\
      ALL (nonoverlapping (z,8 * val p))
          [(word pc,LENGTH bignum_add_windows_tmc); (word_sub stackpointer (word 16),24)] /\
      (x = z \/ nonoverlapping(x,8 * val m) (z,8 * val p)) /\
      (y = z \/ nonoverlapping(y,8 * val n) (z,8 * val p))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_add_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [p;z;m;x;n;y] s /\
                bignum_from_memory (x,val m) s = a /\
                bignum_from_memory (y,val n) s = b)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,val p) s =
                (a + b) MOD 2 EXP (64 * val p) /\
                2 EXP (64 * val p) * val(WINDOWS_C_RETURN s) +
                bignum_from_memory (z,val p) s =
                lowdigits a (val p) + lowdigits b (val p))
           (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bignum(z,val p);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`,
  REWRITE_TAC[WINDOWS_ABI_STACK_THM] THEN
  GEN_X86_ADD_RETURN_STACK_TAC (X86_MK_EXEC_RULE bignum_add_windows_tmc)
    BIGNUM_ADD_WINDOWS_CORRECT
    `[RDI; RSI]` 16 (8,3));;

let BIGNUM_ADD_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!p z m x a n y b pc stackpointer returnaddress.
      ALL (nonoverlapping (word_sub stackpointer (word 16),16))
          [(word pc,LENGTH bignum_add_windows_mc); (x,8 * val m); (y,8 * val n)] /\
      ALL (nonoverlapping (z,8 * val p))
          [(word pc,LENGTH bignum_add_windows_mc); (word_sub stackpointer (word 16),24)] /\
      (x = z \/ nonoverlapping(x,8 * val m) (z,8 * val p)) /\
      (y = z \/ nonoverlapping(y,8 * val n) (z,8 * val p))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_add_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [p;z;m;x;n;y] s /\
                bignum_from_memory (x,val m) s = a /\
                bignum_from_memory (y,val n) s = b)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,val p) s =
                (a + b) MOD 2 EXP (64 * val p) /\
                2 EXP (64 * val p) * val(WINDOWS_C_RETURN s) +
                bignum_from_memory (z,val p) s =
                lowdigits a (val p) + lowdigits b (val p))
           (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bignum(z,val p);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_ADD_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

