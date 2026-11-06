(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Simple interval reasoning tools for expressions involving val/bitval.     *)
(* ========================================================================= *)

let PURE_BOUNDER_RULE =
  let is_add = is_binop `( + ):real->real->real`
  and is_sub = is_binop `( - ):real->real->real`
  and is_mul = is_binop `( * ):real->real->real`
  and is_pow = is_binop `( pow ):real->num->real`
  and is_neg =
    let t = `(--):real->real` in
    fun tm -> is_comb tm && rator tm = t
  and is_abs =
    let t = `abs:real->real` in
    fun tm -> is_comb tm && rator tm = t
  and is_inv =
    let t = `inv:real->real` in
    fun tm -> is_comb tm && rator tm = t
  and is_div = is_binop `( / ):real->real->real`
  and is_ndiv tm = match tm with
      Comb(Const("real_of_num",_),
           Comb(Comb(Const("DIV",_),_),n)) ->
        is_numeral n && dest_numeral n >/ num_0
    | _ -> false
  and is_nmod tm = match tm with
      Comb(Const("real_of_num",_),
           Comb(Comb(Const("MOD",_),_),n)) ->
        is_numeral n && dest_numeral n >/ num_0
    | _ -> false
  and is_nsub tm = match tm with
      Comb(Const("real_of_num",_),
           Comb(Comb(Const("-",_),_),n)) -> true
    | _ -> false
  and is_ncomp tm = match tm with
      Comb(Const("real_of_num",_),
           Comb(Comb(Const(op,_),_),_)) ->
               op = "+" || op = "*" || op = "EXP" ||
               op = "MAX" || op = "MIN"
   | Comb(Const("real_of_num",_),
           Comb(Const("SUC",_),_)) -> true
   | Comb(Const("real_of_num",_),t) -> is_cond t
   | _ -> false
  and is_idiv tm = match tm with
      Comb(Const("real_of_int",_),
           Comb(Comb(Const("div",_),_),n)) ->
        is_intconst n && dest_intconst n >/ num_0
    | _ -> false
  and is_irem tm = match tm with
      Comb(Const("real_of_int",_),
           Comb(Comb(Const("rem",_),_),n)) ->
        is_intconst n && dest_intconst n >/ num_0
    | _ -> false
  and is_icomp tm = match tm with
      Comb(Const("real_of_int",_),
           Comb(Comb(Const(op,_),_),_)) ->
               op = "int_add" || op = "int_sub" ||
               op = "int_mul" || op = "int_pow" ||
               op = "int_max" || op = "int_min"
    | Comb(Const("real_of_int",_),
           Comb(Const(op,_),_)) ->
               op = "int_abs" || op = "int_sgn" ||
               op = "int_neg" || op = "int_of_num"
   | Comb(Const("real_of_int",_),t) -> is_cond t
   | _ -> false
  and modular_upperbound = prove
   (`!m n. ~(n = 0) ==> &(m MOD n) <= &(n - 1)`,
    REWRITE_TAC[REAL_OF_NUM_LE] THEN
    SIMP_TAC[ARITH_RULE `~(n = 0) ==> (m <= n - 1 <=> m < n)`] THEN
    REWRITE_TAC[MOD_LT_EQ])
  and NUMPUSH_CONV =
    GEN_REWRITE_CONV I
     [GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_CLAUSES;
      MESON[] `&(if p then m else n):real = if p then &m else &n`]
  and INTPUSH_CONV =
    GEN_REWRITE_CONV I
     [GSYM REAL_OF_INT_CLAUSES;
      MESON[] `real_of_int(if p then m else n):real =
              if p then real_of_int m else real_of_int n`]
  and BIRATIONAL_RULE =
    CONV_RULE (BINOP2_CONV (LAND_CONV REAL_RAT_REDUCE_CONV)
                           (RAND_CONV REAL_RAT_REDUCE_CONV)) in
  let rule_const tm = let th = SPEC tm REAL_LE_REFL in CONJ th th
  and rule_cconst =
     let pth = REAL_ARITH `!x c:real. x = c ==> c <= x /\ x <= c` in
     fun tm -> let th = REAL_RAT_REDUCE_CONV tm in
               let tm' = rand(concl th) in
               if is_ratconst tm' then MP (SPECL [tm;tm'] pth) th
               else failwith ("BOUNDER_RULE: unhandled term: "
                  ^ (string_of_term tm))
  and rule_div = GEN_REWRITE_CONV I [real_div]
  and rule_vid th = GEN_REWRITE_RULE
                     (fun c ->BINOP2_CONV (RAND_CONV c) (LAND_CONV c))
                     [SYM th]
  and rule_neg =
    let pth = REAL_ARITH
     `!l u x:real. l <= x /\ x <= u ==> --u <= --x /\ --x <= --l` in
    BIRATIONAL_RULE o MATCH_MP pth
  and rule_abs =
    let pth = prove
     (`!l u x:real. l <= x /\ x <= u
                    ==> (if real_sgn l = real_sgn u
                         then min (abs l) (abs u) else &0) <= abs x /\
                        abs(x) <= max (abs l) (abs u)`,
      REWRITE_TAC[REAL_SGNS_EQ] THEN REAL_ARITH_TAC) in
    BIRATIONAL_RULE o MATCH_MP pth
  and rule_add =
    let pth = REAL_ARITH
     `!l1 u1 l2 u2 x y:real.
        (l1 <= x /\ x <= u1) /\
        (l2 <= y /\ y <= u2)
        ==> l1 + l2 <= x + y /\ x + y <= u1 + u2` in
    let rule = MATCH_MP pth in
    fun th1 th2 -> BIRATIONAL_RULE (rule (CONJ th1 th2))
  and rule_cond =
    let pth = REAL_ARITH
     `!l1 u1 l2 u2 x (y:real).
        (l1 <= x /\ x <= u1) /\
        (l2 <= y /\ y <= u2)
        ==> !p. min l1 l2 <= (if p then x else y) /\
                (if p then x else y) <= max u1 u2` in
    let rule = MATCH_MP pth in
    fun p th1 th2 -> BIRATIONAL_RULE (SPEC p (rule (CONJ th1 th2)))
  and rule_sub =
    let pth = REAL_ARITH
     `!l1 u1 l2 u2 x y:real.
        (l1 <= x /\ x <= u1) /\
        (l2 <= y /\ y <= u2)
        ==> l1 - u2 <= x - y /\ x - y <= u1 - l2` in
    let rule = MATCH_MP pth in
    fun th1 th2 -> BIRATIONAL_RULE (rule (CONJ th1 th2))
  and rule_mul =
    let lemma = prove
     (`l:real <= x /\ x <= u
       ==> !a. a * l <= a * x /\ a * x <= a * u \/
               a * u <= a * x /\ a * x <= a * l`,
      MESON_TAC[REAL_LE_NEGTOTAL; REAL_LE_LMUL;
                REAL_ARITH `a * x <= a * y <=> --a * y <= --a * x`]) in
    let pth = prove
      (`!l1 u1 l2 u2 x y:real.
        (l1 <= x /\ x <= u1) /\
        (l2 <= y /\ y <= u2)
        ==> min (l1 * l2) (min (l1 * u2) (min (u1 * l2) (u1 * u2))) <= x * y /\
            x * y <= max (l1 * l2) (max (l1 * u2) (max (u1 * l2) (u1 * u2)))`,
      REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [IMP_CONJ_ALT] THEN
      DISCH_THEN(ASSUME_TAC o SPEC `x:real` o MATCH_MP lemma) THEN
      DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN DISCH_THEN(fun th ->
        MP_TAC(SPEC `l2:real` th) THEN MP_TAC(SPEC `u2:real` th)) THEN
      ASM_REAL_ARITH_TAC) in
    let rule = MATCH_MP pth in
    fun th1 th2 -> BIRATIONAL_RULE (rule (CONJ th1 th2))
  and rule_pow =
    let pth = prove
     (`l:real <= x /\ x <= u
       ==> !n. if EVEN n
               then (if real_sgn l = real_sgn u
                     then min (abs l) (abs u) pow n else &0) <= x pow n /\
                    x pow n <= (max (abs l) (abs u)) pow n
               else l pow n <= x pow n /\ x pow n <= u pow n`,
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[REAL_POW_LE2_ODD; GSYM NOT_EVEN] THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o
        REWRITE_RULE[EVEN_EXISTS]) THEN
      REWRITE_TAC[GSYM REAL_POW_POW] THEN
      ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
      REWRITE_TAC[REAL_POW_POW] THEN
      COND_CASES_TAC THEN REPEAT STRIP_TAC THEN
      SIMP_TAC[REAL_POW_LE; REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN TRY ASM_REAL_ARITH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_SGNS_EQ]) THEN
      ASM_REAL_ARITH_TAC) in
    let rule = MATCH_MP pth
    and cass =
      CONV_RULE(RATOR_CONV (LAND_CONV NUM_EVEN_CONV) THENC
                GEN_REWRITE_CONV I [COND_CLAUSES]) in
    fun th n -> BIRATIONAL_RULE (cass (SPEC n (rule th)))
  and rule_ndiv =
   let pth = prove
    (`!(l:real) u x.
        l <= &x /\ &x <= u
        ==> !n m. ~(&n = &0) /\ u < (&m + &1) * &n
                  ==> &0:real <= &(x DIV n) /\ &(x DIV n):real <= &m`,
     REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN REPEAT STRIP_TAC THEN
     ASM_SIMP_TAC[LE_LDIV_EQ] THEN REPEAT(POP_ASSUM MP_TAC) THEN
     REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC) in
    let rule = MATCH_MP pth in
    fun n th ->
      let m = floor_num(rat_of_term(rand(rand(concl th))) //
                        dest_numeral n) in
      let ith = SPECL [n; mk_numeral m] (rule th) in
      MP ith (EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl ith))))
  and rule_nmod =
    let pth = prove
     (`!(l:real) u x.
         l <= &x /\ &x <= u
         ==> !n. (n = 0 <=> F)
                 ==> &0:real <= &(x MOD n) /\
                     &(x MOD n):real <= min u (&n - &1)`,
      REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_POS] THEN
      REWRITE_TAC[REAL_ARITH `x:real <= min a b <=> x <= a /\ x <= b`] THEN
      CONJ_TAC THENL
       [TRANS_TAC REAL_LE_TRANS `&x:real` THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES; MOD_LE];
        REWRITE_TAC[REAL_LE_SUB_LADD; REAL_OF_NUM_CLAUSES] THEN
        ASM_REWRITE_TAC[ARITH_RULE `x + 1 <= n <=> x < n`; MOD_LT_EQ]]) in
    let rule = MATCH_MP pth in
    fun n th -> let ith = SPEC n (rule th) in
                let nth = NUM_EQ_CONV(lhand(lhand(concl ith))) in
                BIRATIONAL_RULE (MP ith nth)
  and rule_nmod_trivial =
    fun t -> let th1 = SPECL [lhand t; rand t] modular_upperbound in
             let th2 = EQF_ELIM(NUM_EQ_CONV(rand(lhand(concl th1)))) in
             let th3 = CONV_RULE (RAND_CONV(RAND_CONV NUM_SUB_CONV))
                                 (MP th1 th2) in
             CONJ (SPEC t REAL_POS) th3
  and rule_nsub =
    let pth = prove
     (`!(l:real) u x.
         l <= &x /\ &x <= u
         ==> !y. &0:real <= &(x - y) /\ &(x - y) <= u`,
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_POS] THEN
      TRANS_TAC REAL_LE_TRANS `&x:real` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN ARITH_TAC) in
    let rule = MATCH_MP pth in
    fun y th -> BIRATIONAL_RULE (SPEC y (rule th))
  and rule_ncomp =
    let pth = REAL_ARITH
     `&n:real = e /\ l <= e /\ e <= u ==> max (&0) l <= &n /\ &n <= u` in
    let rule = MATCH_MP pth in
    fun eth bth -> BIRATIONAL_RULE(rule (CONJ eth bth))
  and rule_idiv =
    let pth = prove
     (`!(l:real) u x.
         l <= real_of_int x /\ real_of_int x <= u
         ==> !n m p. &0:real < &n /\
                     real_of_int m * &n <= l /\
                     u < (real_of_int p + &1) * &n
                     ==> real_of_int m <= real_of_int(x div &n) /\
                         real_of_int(x div &n) <= real_of_int p`,
      REWRITE_TAC[REAL_OF_NUM_CLAUSES; REAL_OF_INT_CLAUSES] THEN
      REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[INT_DIV_LE_EQ; INT_LE_DIV_EQ; INT_OF_NUM_LT] THEN
      REPEAT(POP_ASSUM MP_TAC) THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN REAL_ARITH_TAC)
    and adj = prove
     (`real_of_int(&n) = &n /\ real_of_int(-- &n) = -- &n`,
      REWRITE_TAC[REAL_OF_INT_CLAUSES]) in
    let rule = MATCH_MP pth
    and ADJ_CONV = GEN_REWRITE_CONV I [adj] in
    fun n th ->
      let ltm,rtm = dest_conj(concl th)
      and n' = dest_numeral n in
      let l' = floor_num(rat_of_term(lhand ltm) // n')
      and r' = floor_num(rat_of_term(rand rtm) // n') in
      let ith = SPECL [n; mk_intconst l'; mk_intconst r'] (rule th) in
      let jth = CONV_RULE
       (BINOP2_CONV
         (RAND_CONV(BINOP2_CONV (LAND_CONV(LAND_CONV ADJ_CONV))
                                (RAND_CONV(LAND_CONV(LAND_CONV ADJ_CONV)))))
         (BINOP2_CONV (LAND_CONV ADJ_CONV) (RAND_CONV ADJ_CONV))) ith in
      MP jth (EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl jth))))
  and rule_irem =
    let pth = prove
     (`!(l:real) u x.
         l <= real_of_int x /\ real_of_int x <= u
         ==> !n. (n = 0 <=> F)
                 ==> &0 <= real_of_int(x rem &n) /\
                     real_of_int(x rem &n) <=
                     (if &0 <= l then min u (&n - &1) else &n - &1)`,
      REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_INT_CLAUSES; INT_REM_POS_EQ; INT_OF_NUM_EQ];
        REWRITE_TAC[COND_RAND; COND_RATOR] THEN
        REWRITE_TAC[REAL_ARITH `x:real <= min a b <=> x <= a /\ x <= b`]] THEN
      REWRITE_TAC[TAUT `(if p then q /\ r else r) <=> r /\ (p ==> q)`] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
        REWRITE_TAC[INT_ARITH `x:int <= n - &1 <=> x < n`] THEN
        ASM_SIMP_TAC[INT_LT_REM_EQ; INT_OF_NUM_LT; LE_1];
        DISCH_TAC THEN
        TRANS_TAC REAL_LE_TRANS `real_of_int x` THEN ASM_REWRITE_TAC[] THEN
        ASM_REWRITE_TAC[REAL_OF_INT_CLAUSES; INT_REM_LE_EQ; INT_OF_NUM_EQ] THEN
        REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN ASM_REAL_ARITH_TAC]) in
    let rule = MATCH_MP pth in
    fun n th -> let ith = SPEC n (rule th) in
                let nth = NUM_EQ_CONV(lhand(lhand(concl ith))) in
                BIRATIONAL_RULE (MP ith nth)
  and rule_irem_trivial =
    let pth = prove
     (`!x n. (n = 0 <=> F)
             ==> &0 <= real_of_int(x rem &n) /\
                 real_of_int(x rem &n) <= &n - &1`,
      REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[INT_ARITH `x:int <= n - &1 <=> x < n`] THEN
      REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ; INT_OF_NUM_CLAUSES] THEN
      ARITH_TAC) in
    fun t -> let ith = SPECL [lhand t; rand(rand t)] pth in
             let nth = NUM_EQ_CONV(lhand(lhand(concl ith))) in
             BIRATIONAL_RULE (MP ith nth)
  and rule_icomp =
    let pth = REAL_ARITH
     `real_of_int x = e /\ l <= e /\ e <= u
      ==> l <= real_of_int x /\ real_of_int x <= u` in
    let rule = MATCH_MP pth in
    fun eth bth -> rule (CONJ eth bth)
  and ron_tm = `real_of_num`
  and roi_tm = `real_of_int` in
  let is_inequality =
    let ineqp = map (can o term_match [])
      [`m:num < n`; `m:num <= n`; `m:num > n`; `m:num >= n`;
       `m:int < n`; `m:int <= n`; `m:int > n`; `m:int >= n`;
       `m:real < n`; `m:real <= n`; `m:real > n`; `m:real >= n`] in
    fun t -> exists (fun f -> f t) ineqp
  and orient_inequality =
    GEN_REWRITE_RULE TRY_CONV [GE; GT; INT_GE; INT_GT; real_ge; real_gt]
  and is_lowerbound = fun (Comb(l,r)) -> frees l = [] && not(frees r = [])
  and is_upperbound = fun (Comb(l,r)) -> not(frees l = []) && frees r = []
  and canonize_lbound =
    let weaken_rule = MATCH_MP REAL_LT_IMP_LE
    and pth_num,pth_lint = (CONJ_PAIR o prove)
     (`((m <= n <=> &m:real <= &n) /\
        (m < n <=> &(m + 1):real <= &n)) /\
       ((a <= b <=> real_of_int a <= real_of_int b) /\
        (a < b <=> real_of_int(a + &1) <= real_of_int b))`,
      REWRITE_TAC[INT_LT_DISCRETE; ARITH_RULE `m < n <=> m + 1 <= n`] THEN
      REWRITE_TAC[GSYM int_le; REAL_OF_NUM_LE]) in
    let typeswitch_conv =
     (GEN_REWRITE_CONV I [pth_num] THENC
     LAND_CONV(RAND_CONV NUM_REDUCE_CONV)) ORELSEC
    (GEN_REWRITE_CONV I [pth_lint] THENC
     LAND_CONV(RAND_CONV INT_REDUCE_CONV) THENC
     GEN_REWRITE_CONV TOP_DEPTH_CONV
      [int_of_num_th; int_neg_th; int_add_th; int_mul_th;
       int_sub_th; int_pow_th; int_abs_th; int_max_th; int_min_th]) in
    fun th ->
      try CONV_RULE typeswitch_conv th with Failure _ ->
      let th' = (try weaken_rule th with Failure _ -> th) in
    CONV_RULE (LAND_CONV REAL_RAT_REDUCE_CONV) th'
  and canonize_ubound =
    let weaken_rule = MATCH_MP REAL_LT_IMP_LE
    and pth_num,pth_int = (CONJ_PAIR o prove)
     (`((m <= n <=> &m:real <= &n) /\
        (m < n <=> &m:real <= &n - &1)) /\
       ((a <= b <=> real_of_int a <= real_of_int b) /\
        (a < b <=> real_of_int a <= real_of_int(b - &1)))`,
      REWRITE_TAC[INT_LT_DISCRETE; ARITH_RULE `m < n <=> m + 1 <= n`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[int_le; int_add_th; int_sub_th; int_of_num_th] THEN
      REAL_ARITH_TAC) in
    let typeswitch_conv =
     (GEN_REWRITE_CONV I [pth_num] THENC
      RAND_CONV(NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV)) ORELSEC
    (GEN_REWRITE_CONV I [pth_int] THENC
     RAND_CONV(RAND_CONV INT_REDUCE_CONV) THENC
     GEN_REWRITE_CONV TOP_DEPTH_CONV
      [int_of_num_th; int_neg_th; int_add_th; int_mul_th;
       int_sub_th; int_pow_th; int_abs_th; int_max_th; int_min_th]) in
    fun th ->
      try CONV_RULE typeswitch_conv th with Failure _ ->
      let th' = (try weaken_rule th with Failure _ -> th) in
    CONV_RULE (RAND_CONV REAL_RAT_REDUCE_CONV) th'
  and default_lowerbounds =
    let valword_lowerbound = prove
     (`&(n MOD 18446744073709551616):real <= &(val(word n:int64))`,
      REWRITE_TAC[VAL_WORD; DIMINDEX_64; ARITH; REAL_LE_REFL])
    and bitvalt_lowerbound = prove
     (`&1:real <= &(bitval T)`,
      REWRITE_TAC[REAL_LE_REFL; BITVAL_CLAUSES])
    and ival_lowerbound = prove
     (`--(&2 pow (dimindex(:N)-1)) <= real_of_int(ival(a:N word))`,
      REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[INT_ARITH `a:int <= b - &1 <=> a < b`; IVAL_BOUND]) in
    let rule_bitvalt_lowerbound = PART_MATCH lhand bitvalt_lowerbound
    and rule_REAL_POS = PART_MATCH rand REAL_POS
    and rule_ival_lowerbound = PART_MATCH rand ival_lowerbound
    and rule_valword_lowerbound = PART_MATCH rand valword_lowerbound in
    fun t ->
      (try [rule_bitvalt_lowerbound t] with Failure _ -> []) @
      (try [rule_REAL_POS t] with Failure _ -> []) @
      (try let th = rule_ival_lowerbound t in
           [CONV_RULE(LAND_CONV
               (RAND_CONV (RAND_CONV(LAND_CONV (!word_SIZE_CONV) THENC
                                     NUM_SUB_CONV) THENC
                           REAL_RAT_POW_CONV) THENC REAL_RAT_NEG_CONV)) th]
       with Failure _ -> []) @
      (try let th1 = rule_valword_lowerbound t in
           let th2 = CONV_RULE(LAND_CONV(RAND_CONV NUM_REDUCE_CONV)) th1 in
           [if is_ratconst(lhand(concl th2)) then th2 else failwith ""]
       with Failure _ -> [])
  and default_upperbounds =
    let bitval_upperbound = prove
     (`!b. &(bitval b):real <= &1`,
      REWRITE_TAC[REAL_OF_NUM_LE; BITVAL_BOUND])
    and bitvalf_upperbound = prove
     (`&(bitval F):real <= &0`,
      REWRITE_TAC[BITVAL_CLAUSES; REAL_LE_REFL])
    and val_upperbound = prove
     (`&(val(a:int64)):real <= &18446744073709551615`,
      MP_TAC(SPEC `a:int64` VAL_BOUND_64) THEN
      REWRITE_TAC[REAL_OF_NUM_LE; DIMINDEX_64] THEN ARITH_TAC)
    and val_upperbound_gen = prove
     (`&(val(a:N word)):real <= &2 pow dimindex(:N) - &1`,
      REWRITE_TAC[REAL_LE_SUB_LADD; REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`; VAL_BOUND])
    and valword_upperbound = prove
     (`&(val(word n:int64)) <= &n`,
      SIMP_TAC[REAL_OF_NUM_LE; VAL_WORD_LE; LE_REFL])
    and lmask_upperbound = prove
     (`&(val(word_and (word n) (a:int64))):real <= &n`,
      REWRITE_TAC[REAL_OF_NUM_LE; VAL_WORD_AND_WORD_LE])
    and rmask_upperbound = prove
     (`&(val(word_and (a:int64) (word n))):real <= &n`,
      REWRITE_TAC[REAL_OF_NUM_LE; VAL_WORD_AND_WORD_LE])
    and shift_upperbound = prove
     (`&(val (word_ushr (a:int64) n)):real <= &2 pow (64 - n) - &1`,
      REWRITE_TAC[REAL_LE_SUB_LADD; VAL_WORD_USHR] THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES; ARITH_RULE `x + 1 <= y <=> x < y`] THEN
      SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
      TRANS_TAC LTE_TRANS `2 EXP 64` THEN REWRITE_TAC[VAL_BOUND_64] THEN
      REWRITE_TAC[LE_EXP] THEN ARITH_TAC)
    and ival_upperbound = prove
     (`real_of_int(ival(a:N word)) <= &2 pow (dimindex(:N)-1) - &1`,
      REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[INT_ARITH `a:int <= b - &1 <=> a < b`; IVAL_BOUND]) in
    let rule_bitvalf_upperbound = PART_MATCH lhand bitvalf_upperbound
    and rule_bitval_upperbound = PART_MATCH lhand bitval_upperbound
    and rule_val_upperbound = PART_MATCH lhand val_upperbound
    and rule_val_upperbound_gen = PART_MATCH lhand val_upperbound_gen
    and rule_ival_upperbound = PART_MATCH lhand ival_upperbound
    and rule_shift_upperbound = PART_MATCH lhand shift_upperbound
    and rule_valword_upperbound = PART_MATCH lhand valword_upperbound
    and rule_lmask_upperbound = PART_MATCH lhand lmask_upperbound
    and rule_rmask_upperbound = PART_MATCH lhand rmask_upperbound
    and rule_modular_upperbound =
      PART_MATCH (lhand o rand) modular_upperbound in
    fun t ->
     (try [rule_bitvalf_upperbound t] with Failure _ -> []) @
     (try [rule_bitval_upperbound t] with Failure _ -> []) @
     (try [rule_val_upperbound t] with Failure _ -> []) @
     (try let th = rule_val_upperbound_gen t in
          [CONV_RULE
            (RAND_CONV
             (LAND_CONV
               (RAND_CONV (!word_SIZE_CONV) THENC REAL_RAT_POW_CONV) THENC
              REAL_RAT_SUB_CONV)) th] with Failure _ -> []) @
     (try let th = rule_ival_upperbound t in
          [CONV_RULE
             (RAND_CONV
                (LAND_CONV (RAND_CONV(LAND_CONV (!word_SIZE_CONV) THENC
                 NUM_SUB_CONV) THENC
              REAL_RAT_POW_CONV) THENC REAL_RAT_SUB_CONV)) th]
     with Failure _ -> []) @
     (try let th1 = rule_shift_upperbound t in
          [CONV_RULE(RAND_CONV
            (LAND_CONV(RAND_CONV NUM_SUB_CONV THENC
                       REAL_RAT_POW_CONV) THENC
             REAL_RAT_SUB_CONV)) th1]
      with Failure _ -> []) @
     (try let th1 = rule_valword_upperbound t in
          let th2 = CONV_RULE(RAND_CONV(RAND_CONV NUM_REDUCE_CONV)) th1 in
          [if is_ratconst(rand(concl th2)) then th2 else failwith ""]
      with Failure _ -> []) @
     (try let th1 = rule_lmask_upperbound t in
          let th2 = CONV_RULE(RAND_CONV(RAND_CONV NUM_REDUCE_CONV)) th1 in
          [if is_ratconst(rand(concl th2)) then th2 else failwith ""]
      with Failure _ -> []) @
     (try let th1 = rule_rmask_upperbound t in
          let th2 = CONV_RULE(RAND_CONV(RAND_CONV NUM_REDUCE_CONV)) th1 in
          [if is_ratconst(rand(concl th2)) then th2 else failwith ""]
      with Failure _ -> []) @
     (try let th = PART_MATCH (lhand o rand) modular_upperbound t in
          let th' = MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))) in
           [CONV_RULE(RAND_CONV(RAND_CONV NUM_REDUCE_CONV)) th']
      with Failure _ -> []) in
  fun ths ->
    let iths = filter (is_inequality o concl) ths in
    let oths = map orient_inequality iths in
    let lbounds =
      filter (is_ratconst o lhand o concl)
             (map canonize_lbound (filter (is_lowerbound o concl) oths))
    and ubounds =
      filter (is_ratconst o rand o concl)
             (map canonize_ubound (filter (is_upperbound o concl) oths)) in
    let basic_lowerbound def t =
      let lbs = filter ((=) t o rand o concl) lbounds @
                (if def then default_lowerbounds t else []) in
      hd(sort (fun s t -> rat_of_term(lhand(concl s)) >/
                          rat_of_term(lhand(concl t))) lbs)
    and basic_upperbound def t =
      let ubs = filter ((=) t o lhand o concl) ubounds @
                (if def then default_upperbounds t else []) in
      hd(sort (fun s t -> rat_of_term(rand(concl s)) </
                          rat_of_term(rand(concl t))) ubs) in
    let rec bounder tm =
      try CONJ (basic_lowerbound false tm) (basic_upperbound false tm)
      with Failure _ ->
        if is_ratconst tm then rule_const tm
        else if is_neg tm then rule_neg (bounder(rand tm))
        else if is_abs tm then rule_abs (bounder(rand tm))
        else if is_add tm then rule_add (bounder(lhand tm)) (bounder(rand tm))
        else if is_sub tm then rule_sub (bounder(lhand tm)) (bounder(rand tm))
        else if is_mul tm then rule_mul (bounder(lhand tm)) (bounder(rand tm))
        else if is_ncomp tm then
          let eth = NUMPUSH_CONV tm in
          let bth = bounder (rand(concl eth)) in
          rule_ncomp eth bth
        else if is_icomp tm then
          let eth = INTPUSH_CONV tm in
          let bth = bounder (rand(concl eth)) in
          rule_icomp eth bth
        else if is_ndiv tm then
          rule_ndiv
           (rand(rand tm))
           (bounder(mk_comb(ron_tm,lhand(rand tm))))
        else if is_idiv tm then
          rule_idiv
           (rand(rand(rand tm)))
           (bounder(mk_comb(roi_tm,lhand(rand tm))))
        else if is_nmod tm then
          try let th = bounder(mk_comb(ron_tm,lhand(rand tm))) in
              rule_nmod (rand(rand tm)) th
          with Failure _ -> rule_nmod_trivial(rand tm)
        else if is_irem tm then
          try let th = bounder(mk_comb(roi_tm,lhand(rand tm))) in
              rule_irem (rand(rand(rand tm))) th
          with Failure _ -> rule_irem_trivial(rand tm)
        else if is_nsub tm then
          rule_nsub (rand(rand tm)) (bounder(mk_comb(ron_tm,lhand(rand tm))))
        else if is_cond tm then
          rule_cond (lhand(rator tm)) (bounder(lhand tm)) (bounder(rand tm))
        else if is_pow tm && is_numeral (rand tm) then
            rule_pow (bounder(lhand tm)) (rand tm)
        else if is_inv tm then rule_cconst tm
        else if is_div tm then
          let eth = rule_div tm in rule_vid eth (bounder(rand(concl eth)))
        else try CONJ (basic_lowerbound true tm) (basic_upperbound true tm)
             with Failure _ -> failwith
              ("BOUNDER_RULE: unhandled term: " ^
                string_of_term tm) in
    bounder;;

let BOUNDER_RULE ths =
  let bounder = PURE_BOUNDER_RULE ths in
  fun tm -> let ith = (REAL_POLY_CONV THENC
                       NUM_REDUCE_CONV THENC
                       INT_REDUCE_CONV) tm in
            let bth = bounder (rand(concl ith)) in
            GEN_REWRITE_RULE
              (fun c -> BINOP2_CONV (RAND_CONV c) (LAND_CONV c))
              [SYM ith] bth;;

(* ------------------------------------------------------------------------- *)
(* Tactic form of bounder.                                                   *)
(* ------------------------------------------------------------------------- *)

let bounder_prenorm_thms = ref ([]: thm list);;

let SHARPEN_INEQ_TAC =
  let pth = prove
   (`(integer x /\ integer y) /\ x < y + &1 ==> x <= y`,
    SIMP_TAC[IMP_CONJ; REAL_LT_INTEGERS; INTEGER_CLOSED] THEN
    REAL_ARITH_TAC) in
  TRY(MATCH_MP_TAC pth THEN CONJ_TAC THENL
       [CONJ_TAC THEN REAL_INTEGER_TAC; ALL_TAC]);;

let (PURE_BOUNDER_TAC:thm list -> tactic),(BOUNDER_TAC:thm list -> tactic) =
  let STANDARDIZE_INEQ_CONV =
    (fun g -> GEN_REWRITE_CONV TOP_DEPTH_CONV(!bounder_prenorm_thms) g) THENC
    GEN_REWRITE_CONV TRY_CONV [GE; GT; INT_GE; INT_GT; real_ge; real_gt] THENC
    GEN_REWRITE_CONV TRY_CONV
     [GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_LE; int_lt; int_le] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV
     [GSYM REAL_OF_NUM_CLAUSES;
      int_abs_th; int_add_th; int_max_th; int_min_th; int_mul_th;
      int_neg_th; int_of_num_th; int_pow_th; int_sgn_th; int_sub_th] THENC
    GEN_REWRITE_CONV I [GSYM REAL_SUB_LE; GSYM REAL_SUB_LT]
  and SHARPEN_INEQ_0_TAC =
    let pth = prove
     (`integer x /\ &0 < x + &1 ==> &0 <= x`,
      SIMP_TAC[IMP_CONJ; REAL_LT_INTEGERS; INTEGER_CLOSED] THEN
      REAL_ARITH_TAC) in
    TRY(MATCH_MP_TAC pth THEN CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC])
  and BASIC_BOUNDER_TAC =
    let patok_le = can (term_match [] `&0:real <= x`)
    and patok_lt = can (term_match [] `&0:real < x`)
    and rule_le =
      MATCH_MP(REAL_ARITH `l:real <= x /\ x <= u ==> &0 <= l ==> &0 <= x`)
    and rule_lt =
      MATCH_MP(REAL_ARITH `l:real <= x /\ x <= u ==> &0 < l ==> &0 < x`) in
    fun boundrule (ths:thm list) (asl,w as gl) ->
      if patok_le w then MATCH_MP_TAC (rule_le(boundrule ths (rand w))) gl
      else if patok_lt w then MATCH_MP_TAC (rule_lt(boundrule ths (rand w))) gl
      else failwith "BASIC_BOUNDER_TAC: Not expected form" in
  let GEN_BOUNDER_TAC baserule ths =
    REPEAT CONJ_TAC THEN
    CONV_TAC STANDARDIZE_INEQ_CONV THEN
    SHARPEN_INEQ_0_TAC THEN
    BASIC_BOUNDER_TAC baserule ths THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC in
  GEN_BOUNDER_TAC PURE_BOUNDER_RULE,GEN_BOUNDER_TAC BOUNDER_RULE;;

(* ------------------------------------------------------------------------- *)
(* Tool to simplify assumptions and possibly prove carries are zero.         *)
(* ------------------------------------------------------------------------- *)

(*** Might be some arguments against saving the restore0 theorem?
 *** It's valid and in principle useful but does slightly change the
 *** fact that the lhs's are variables to eliminate.
 ***)

let GEN_DECARRY_RULE =
  let simper1 = MATCH_MP (REAL_ARITH
    `&2 pow 64 * hi + lo:real = z
     ==> hi = (z - lo) / &18446744073709551616`)
  and simper0 = MATCH_MP (REAL_ARITH
    `&2 pow 64 * hi:real = z
     ==> hi = z / &18446744073709551616`)
  and simper3 = MATCH_MP (REAL_ARITH
    `--(&2 pow 64) * hi + lo:real = z
     ==> hi = (lo - z) / &18446744073709551616`)
  and simper2 = MATCH_MP (REAL_ARITH
    `--(&2 pow 64) * hi:real = z
     ==> hi = --z / &18446744073709551616`)
  and uncarry = (MATCH_MP o prove)
   (`&b:real = t /\ (l <= t /\ t <= u)
     ==> u < &1 ==> &b:real = &0`,
    REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_RULE `n = 0 <=> n < 1`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN REAL_ARITH_TAC)
  and upcarry = (MATCH_MP o prove)
  (`&(bitval b):real = t /\ (l <= t /\ t <= u)
     ==> &0 < l ==> &(bitval b):real = &1`,
   BOOL_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
   REAL_ARITH_TAC)
  and restore1 = (MATCH_MP o REAL_ARITH)
   `&2 pow 64 * hi + lo:real = z /\ hi = &0 ==> lo = z`
  and restore0 = (MATCH_MP o REAL_ARITH)
   `&2 pow 64 * hi:real = z /\ hi = &0 ==> z = &0`
  and restore3 = (MATCH_MP o REAL_ARITH)
   `--(&2 pow 64) * hi + lo:real = z /\ hi = &0 ==> lo = z`
  and restore2 = (MATCH_MP o REAL_ARITH)
   `--(&2 pow 64) * hi:real = z /\ hi = &0 ==> z = &0`
  and destore1 = (MATCH_MP o REAL_ARITH)
   `&2 pow 64 * hi + lo:real = z /\ hi = &1 ==> lo = z - &2 pow 64`
  and destore0 = (MATCH_MP o REAL_ARITH)
   `&2 pow 64 * hi:real = z /\ hi = &1 ==> z = &2 pow 64`
  and destore3 = (MATCH_MP o REAL_ARITH)
   `--(&2 pow 64) * hi + lo:real = z /\ hi = &1 ==> lo = z + &2 pow 64`
  and destore2 = (MATCH_MP o REAL_ARITH)
   `--(&2 pow 64) * hi:real = z /\ hi = &1 ==> z = --(&2 pow 64)`
  and bitty = can (term_match [] `&(bitval b):real`) in
  let simper th =
    try simper1 th with Failure _ ->
    try simper0 th with Failure _ ->
    try simper3 th with Failure _ ->
    simper2 th
  and restore th =
    let th' =
      try restore1 th with Failure _ ->
      try restore0 th with Failure _ ->
      try restore3 th with Failure _ ->
      restore2 th in
    let l,r = dest_eq(concl th') in
    if l = r then [] else [th']
  and destore th =
    let th' =
      try destore1 th with Failure _ ->
      try destore0 th with Failure _ ->
      try destore3 th with Failure _ ->
      destore2 th in
    let l,r = dest_eq(concl th') in
    if l = r then [] else [th'] in
  fun boths ->
    let rec zonker ths =
      match ths with
        [] -> []
      | th::oths ->
            let oths' = zonker oths in
            let th' =
              CONV_RULE (RAND_CONV(PURE_REWRITE_CONV oths' THENC
                                   REAL_POLY_CONV))
                        (simper th) in
            let etm = concl th' in
            let lrth = time (BOUNDER_RULE boths) (rand etm) in
            if rat_of_term(rand(rand(concl lrth))) </ num_1 then
              let ith = uncarry (CONJ th' lrth) in
              let bth = REAL_RAT_LT_CONV(lhand(concl ith)) in
              let th'' = MP ith (EQT_ELIM bth) in
              th''::(restore (CONJ th th'') @ oths')
            else if bitty(lhand etm) &&
                    rat_of_term(lhand(lhand(concl lrth))) >/ num_0 then
              let ith = upcarry (CONJ th' lrth) in
              let bth = REAL_RAT_LT_CONV(lhand(concl ith)) in
              let th'' = MP ith (EQT_ELIM bth) in
              th''::(destore (CONJ th th'') @ oths')
            else
              th'::oths' in
  zonker;;

let DECARRY_RULE = GEN_DECARRY_RULE [];;

(* ------------------------------------------------------------------------- *)
(* A dual that replaces the sum, but doesn't try to prove any bounds. The    *)
(* idea here is just to collect the "ignored high parts" explicitly.         *)
(* ------------------------------------------------------------------------- *)

let DESUM_RULE =
  let simper1 = MATCH_MP (REAL_ARITH
    `&2 pow 64 * hi + lo:real = z
     ==> lo = z - &18446744073709551616 * hi`)
  and simper0 = MATCH_MP (REAL_ARITH
    `&2 pow 64 * hi:real = z
     ==> hi = z / &18446744073709551616`)
  and simper3 = MATCH_MP (REAL_ARITH
    `--(&2 pow 64) * hi + lo:real = z
     ==> lo = z + &18446744073709551616 * hi`)
  and simper2 = MATCH_MP (REAL_ARITH
    `--(&2 pow 64) * hi:real = z
     ==> hi = --z / &18446744073709551616`) in
  let simper th =
    try simper1 th with Failure _ ->
    try simper0 th with Failure _ ->
    try simper3 th with Failure _ ->
    simper2 th in
  let rec zonker ths =
    match ths with
      [] -> []
    | th::oths ->
          let oths' = zonker oths in
          let th' =
            CONV_RULE (RAND_CONV(PURE_REWRITE_CONV oths' THENC
                                 REAL_POLY_CONV))
                      (simper th) in
          th'::oths' in
  zonker;;

(* ------------------------------------------------------------------------- *)
(* Do something with the "accumulator" assumptions, removing them            *)
(* in the "POP" case, and in both cases applying a few rewrites.             *)
(* ------------------------------------------------------------------------- *)

let ACCUMULATOR_DEFAULT_REWRITE_RULE =
  let REAL_VAL_WORD_MASK_64 = prove
   (`!b. &(val(word_neg(word(bitval b):int64))):real =
         (&2 pow 64 - &1) * &(bitval b)`,
    REWRITE_TAC[REAL_VAL_WORD_MASK; DIMINDEX_64])
  and REAL_VAL_WORD_NOT_64 = prove
   (`!x:int64. &(val(word_not x)) = &2 pow 64 - &1 - &(val x)`,
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64]) in
  GEN_REWRITE_RULE (RAND_CONV o TOP_DEPTH_CONV)
    [VAL_WORD_BITVAL; VAL_WORD_0; VAL_WORD_1;
     REAL_VAL_WORD_MASK_64; REAL_VAL_WORD_NOT_64];;

let ACCUMULATOR_ASSUM_LIST:(thm list -> tactic) -> tactic =
  let mf1 = can (term_match [] `&2 pow 64 * c + h:real = x`)
  and mf2 = can (term_match [] `--(&2 pow 64) * c + h:real = x`) in
  let mfn th = let t = concl th in mf1 t || mf2 t in
  fun ttac (asl,w) ->
    ttac (map ACCUMULATOR_DEFAULT_REWRITE_RULE
              (filter mfn (map snd asl))) (asl,w);;

let ACCUMULATOR_POP_ASSUM_LIST:(thm list -> tactic) -> tactic =
  let mf1 = can (term_match [] `&2 pow 64 * c + h:real = x`)
  and mf2 = can (term_match [] `--(&2 pow 64) * c + h:real = x`) in
  let mfn th = let t = concl th in mf1 t || mf2 t in
  fun ttac ->
   POP_ASSUM_LIST
    (fun ths -> let ths1,ths2 = partition mfn ths in
                MAP_EVERY ASSUME_TAC (rev ths2) THEN
                ttac (map ACCUMULATOR_DEFAULT_REWRITE_RULE ths1));;

(* ------------------------------------------------------------------------- *)
(* A beefed-up but very naive ARITH_RULE that also pulls in the              *)
(* knowledge of the bounds of subterms "val n" and "bitval b".               *)
(* ------------------------------------------------------------------------- *)

let VAL_ARITH_RULE =
  let init_conv =
    DEPTH_CONV(GEN_REWRITE_CONV I [BITVAL_CLAUSES] ORELSEC
               WORD_RED_CONV ORELSEC
               NUM_RED_CONV)
  and is_bit t = match t with
      Comb(Const("bitval",_),_) -> true | _ -> false
  and is_val t = match t with
      Comb(Const("val",_),_) -> true | _ -> false
  and bth_val t =
    CONV_RULE (RAND_CONV(TRY_CONV(!word_POW2SIZE_CONV)))
              (PART_MATCH lhand VAL_BOUND t)
  and bth_bit = PART_MATCH lhand BITVAL_BOUND in
  fun tm ->
    let ith = init_conv tm in
    let tm' = rand(concl ith) in
    let btms = find_terms is_bit tm'
    and vtms = find_terms is_val tm' in
    let bths = map bth_bit btms @ map bth_val vtms in
    let atm = itlist (curry mk_imp o concl) bths tm' in
    let ath = ARITH_RULE atm in
    EQ_MP (SYM ith) (rev_itlist (C MP) bths ath);;

(* ------------------------------------------------------------------------- *)
(* Accumulation tactic, useful for reasoning about carry chains.             *)
(* - reduce val(word n) for particular n                                     *)
(* - express everything in a sign-natural way over R.                        *)
(* - keyed to a specific state                                               *)
(* - tries to work in a unified way for ARM and x86, both carry flags        *)
(* - secondary triggering from zero flag if result is not written (ARM xzr)  *)
(* - includes a similar accumulation for "extr" with a zero register.        *)
(* - ditto word_ushr and word_ushl (which are effectively the same)          *)
(* - the X version excludes writes to certain registers (components)         *)
(* ------------------------------------------------------------------------- *)

let ACCUMULATEX_ARITH_TAC =
  let int64_ty = `:int64`
  and patfn = can (term_match [] `read Xnn s = e`)
  and pth_zerotrig = prove
   (`(read ZZ s <=> val(a:int64) = 0) ==> read (rvalue a) s = a`,
    REWRITE_TAC[READ_RVALUE])
  and pth_adc = prove
   (`!(s:S) Xnn (x:int64) y b.
        read Xnn s = word_add (word_add x y) (word(bitval b))
        ==> ?c z. (&2 pow 64 * &(bitval c) + &(val z):real =
                   &(val x) + &(val y) + &(bitval b) /\
                   read Xnn s = z) /\
                  ((2 EXP 64 <= val x + val y + bitval b) <=> c) /\
                  ((val x + val y + bitval b < 2 EXP 64) <=> ~c)`,
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_ADD;
                REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN
    REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`2 EXP 64 <= val(x:int64) + val(y:int64) + bitval b`;
      `word_add (word_add x y) (word(bitval b)):int64`] THEN
    ASM_REWRITE_TAC[GSYM ACCUMULATE_ADC; VAL_WORD_BITVAL; NOT_LE])
  and pth_sbc = prove
   (`!(s:S) Xnn (x:int64) y b.
        read Xnn s = word_sub x (word_add y (word(bitval b)))
        ==> ?c z. (--(&2 pow 64) * &(bitval c) + &(val z):real =
                   &(val x) - &(val y) - &(bitval b) /\
                   read Xnn s = z) /\
                  (val x < val y + bitval b <=> c) /\
                  (val y + bitval b <= val x <=> ~c)`,
    REWRITE_TAC[REAL_ARITH `--e * c + z:real = x - y - b <=>
                            e * c + x = y + b + z`] THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_ADD;
                REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN
    REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`val(x:int64) < val(y:int64) + bitval b`;
      `word_sub x (word_add y (word(bitval b))):int64`] THEN
    ASM_REWRITE_TAC[ACCUMULATE_SBB; NOT_LT] THEN ARITH_TAC)
  and pth_sub = prove
   (`!(s:S) Xnn x y:int64.
        read Xnn s = word_sub x y
        ==> ?c z. (--(&2 pow 64) * &(bitval c) + &(val z):real =
                   &(val x) - &(val y) /\
                   read Xnn s = z) /\
                  (val x < val y <=> c) /\
                  (val y <= val x <=> ~c)`,
    REWRITE_TAC[REAL_ARITH `--e * c + z:real = x - y <=>
                            e * c + x = y + z`] THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_ADD;
                REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN
    REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`val(x:int64) < val(y:int64)`;
      `word_sub x y:int64`] THEN
    ASM_REWRITE_TAC[ACCUMULATE_SUB; NOT_LT] THEN ARITH_TAC)
  and pth_mul_hi = prove
   (`!(s:S) Xnn (x:int64) (y:int64).
       read Xnn s :int64 =
       word_zx (word_ushr (word (val x * val y):int128)
               64)
        ==> ?(h:int64) (l:int64).
               (&2 pow 64 * &(val h) + &(val l):real = &(val x) * &(val y) /\
                read Xnn s = h) /\
               word_zx(word(val x * val y):int128):int64 = l`,
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN MESON_TAC[ACCUMULATE_MUL])
  and pth_mul_lo = prove
   (`!(s:S) Xnn (x:int64) (y:int64).
       read Xnn s :int64 = word_zx(word(val x * val y):int128)
        ==> ?(h:int64) (l:int64).
               (&2 pow 64 * &(val h) + &(val l):real = &(val x) * &(val y) /\
                read Xnn s = l) /\
               word_zx (word_ushr (word (val x * val y):int128)
                       64) = h`,
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN MESON_TAC[ACCUMULATE_MUL])
  and pth_mul_hi2 = prove
   (`!(s:S) Xnn (x:int64) (y:int64).
        read Xnn s :int64 =
        word((val x * val y) DIV 2 EXP 64)
        ==> ?(h:int64) (l:int64).
               (&2 pow 64 * &(val h) + &(val l):real = &(val x) * &(val y) /\
                read Xnn s = h) /\
               (word(0 + val x * val y) = l /\
                word(val x * val y) = l)`,
    REPEAT GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
    GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [WORD_MUL; WORD_VAL] THEN
    REWRITE_TAC[WORD_MULTIPLICATION_LOHI_64] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN MESON_TAC[ACCUMULATE_MUL])
  and pth_mul_lo2 = prove
   (`!(s:S) Xnn (x:int64) (y:int64).
        read Xnn s :int64 = word(0 + val x * val y)
        ==> ?(h:int64) (l:int64).
               (&2 pow 64 * &(val h) + &(val l):real = &(val x) * &(val y) /\
                read Xnn s = l) /\
               (word((val x * val y) DIV 2 EXP 64) = h /\
                word(val x * val y) = l)`,
    REWRITE_TAC[ADD_CLAUSES; WORD_MUL; WORD_VAL] THEN
    REWRITE_TAC[WORD_MULTIPLICATION_LOHI_64] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN MESON_TAC[ACCUMULATE_MUL])
  and pth_ushr = prove
   (`!(s:S) Xnn (x:int64) k.
          read Xnn s = word_ushr x k
          ==> k < 64
              ==> ?(h:int64) (l:int64).
                      (&2 pow 64 * &(val h) + &(val l):real =
                        &2 pow (64 - k) * &(val x) /\
                       read Xnn s = h) /\
                      word_shl x (64 - k) = l /\
                      word_subword (word_join x (word 0:int64):int128)
                                   (k,64) = l`,
    REPEAT STRIP_TAC THEN EXISTS_TAC `read (Xnn:(S,int64)component) s` THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN
    ASM_REWRITE_TAC[UNWIND_THM1; GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[WORD_SUBWORD_JOIN_AS_SHL; DIMINDEX_64; LT_IMP_LE];
      REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_SHL; VAL_WORD_USHR]] THEN
    MATCH_MP_TAC(MESON[DIVISION_SIMP]
     `x = n * y DIV n ==> x + y MOD n = y`) THEN
    REWRITE_TAC[DIMINDEX_64] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `2 EXP 64 = 2 EXP (64 - k) * 2 EXP k` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ]]) in
  let pth_extr = prove
   (`!(s:S) Xnn (x:int64) k.
          read Xnn s = word_subword (word_join (word 0:int64) x :int128)
                                    (k,64)
          ==> k < 64
              ==> ?(h:int64) (l:int64).
                      (&2 pow 64 * &(val h) + &(val l):real =
                        &2 pow (64 - k) * &(val x) /\
                       read Xnn s = h) /\
                      word_shl x (64 - k) = l /\
                      word_subword (word_join x (word 0:int64):int128)
                                   (k,64) = l`,
    REPEAT GEN_TAC THEN REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] pth_ushr) THEN
    ASM_REWRITE_TAC[GSYM WORD_SUBWORD_JOIN_AS_USHR; DIMINDEX_64])
  and pth_mul_hil = prove
   (`!(s:S) Xnn n (y:int64).
        read Xnn s :int64 =
        word_zx (word_ushr (word (NUMERAL n * val y):int128)
                64)
        ==> NUMERAL n < 2 EXP 64
            ==> ?(h:int64) (l:int64).
                   (&2 pow 64 * &(val h) + &(val l):real =
                    &(NUMERAL n) * &(val y) /\
                    read Xnn s = h) /\
                   word_zx(word(NUMERAL n * val y):int128):int64 = l`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:S`; `Xnn:(S,int64)component`;
                   `word(NUMERAL n):int64`; `y:int64`]
          pth_mul_hi) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT])
  and pth_mul_lol = prove
     (`!(s:S) Xnn n (y:int64).
         read Xnn s :int64 = word_zx(word(NUMERAL n * val y):int128)
          ==> NUMERAL n < 2 EXP 64
            ==> ?(h:int64) (l:int64).
                   (&2 pow 64 * &(val h) + &(val l):real =
                    &(NUMERAL n) * &(val y) /\
                    read Xnn s = l) /\
                   word_zx (word_ushr (word (NUMERAL n * val y):int128)
                           64) = h`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:S`; `Xnn:(S,int64)component`;
                   `word(NUMERAL n):int64`; `y:int64`]
          pth_mul_lo) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT])
  and pth_mul_hir = prove
   (`!(s:S) Xnn (x:int64) n.
        read Xnn s :int64 =
        word_zx (word_ushr (word (val x * NUMERAL n):int128)
                64)
        ==> NUMERAL n < 2 EXP 64
            ==> ?(h:int64) (l:int64).
                   (&2 pow 64 * &(val h) + &(val l):real =
                    &(val x) * &(NUMERAL n) /\
                    read Xnn s = h) /\
                   word_zx(word(val x * NUMERAL n):int128):int64 = l`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:S`; `Xnn:(S,int64)component`;
                   `x:int64`; `word(NUMERAL n):int64`]
          pth_mul_hi) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT])
  and pth_mul_lor = prove
     (`!(s:S) Xnn (x:int64) n.
         read Xnn s :int64 = word_zx(word(val x * NUMERAL n):int128)
          ==> NUMERAL n < 2 EXP 64
            ==> ?(h:int64) (l:int64).
                   (&2 pow 64 * &(val h) + &(val l):real =
                    &(val x) * &(NUMERAL n) /\
                    read Xnn s = l) /\
                   word_zx (word_ushr (word (val x * NUMERAL n):int128)
                           64) = h`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:S`; `Xnn:(S,int64)component`;
                   `x:int64`; `word(NUMERAL n):int64`]
          pth_mul_lo) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT])
  and pth_mul_hil2 = prove
   (`!(s:S) Xnn n (y:int64).
        read Xnn s :int64 =
        word((NUMERAL n * val y) DIV 2 EXP 64)
        ==> NUMERAL n < 2 EXP 64
            ==> ?(h:int64) (l:int64).
                     (&2 pow 64 * &(val h) + &(val l):real =
                      &(NUMERAL n) * &(val y) /\
                      read Xnn s = h) /\
                     (word(0 + NUMERAL n * val y) = l /\
                      word(NUMERAL n * val y) = l)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:S`; `Xnn:(S,int64)component`;
                   `word(NUMERAL n):int64`; `y:int64`]
          pth_mul_hi2) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT])
  and pth_mul_lol2 = prove
   (`!(s:S) Xnn n (y:int64).
        read Xnn s :int64 = word(0 + NUMERAL n * val y)
        ==> NUMERAL n < 2 EXP 64
            ==> ?(h:int64) (l:int64).
                     (&2 pow 64 * &(val h) + &(val l):real =
                      &(NUMERAL n) * &(val y) /\
                      read Xnn s = l) /\
                     (word((NUMERAL n * val y) DIV 2 EXP 64) = h /\
                      word(NUMERAL n * val y) = l /\
                      word((val(word(NUMERAL n):int64) * val y)
                           DIV 2 EXP 64) = h /\
                      word(val(word(NUMERAL n):int64) * val y) = l)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:S`; `Xnn:(S,int64)component`;
                   `word(NUMERAL n):int64`; `y:int64`]
          pth_mul_lo2) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT] THEN MESON_TAC[])
  and pth_mul_hir2 = prove
   (`!(s:S) Xnn (x:int64) n.
        read Xnn s :int64 =
        word((val x * NUMERAL n) DIV 2 EXP 64)
        ==> NUMERAL n < 2 EXP 64
            ==> ?(h:int64) (l:int64).
                     (&2 pow 64 * &(val h) + &(val l):real =
                      &(val x) * &(NUMERAL n) /\
                      read Xnn s = h) /\
                     (word(0 + val x * NUMERAL n) = l /\
                      word(val x * NUMERAL n) = l)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:S`; `Xnn:(S,int64)component`;
                   `x:int64`; `word(NUMERAL n):int64`]
          pth_mul_hi2) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT])
  and pth_mul_lor2 = prove
   (`!(s:S) Xnn (x:int64) n.
        read Xnn s :int64 = word(0 + val x * NUMERAL n)
        ==> NUMERAL n < 2 EXP 64
            ==> ?(h:int64) (l:int64).
                    (&2 pow 64 * &(val h) + &(val l):real =
                     &(val x) * &(NUMERAL n) /\
                     read Xnn s = l) /\
                    (word((val x * NUMERAL n) DIV 2 EXP 64) = h /\
                     word(val x * NUMERAL n) = l /\
                     word((val x * val(word(NUMERAL n):int64)) DIV
                          2 EXP 64) = h /\
                     word(val x * val(word(NUMERAL n):int64)) = l)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:S`; `Xnn:(S,int64)component`;
                   `x:int64`; `word(NUMERAL n):int64`]
          pth_mul_lo2) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT] THEN MESON_TAC[])
  and pth_sbc_rn = prove
   (`!(s:S) Xnn (x:int64) n b.
        read Xnn s = word_sub x (word(n + bitval b))
        ==> ?c z. (--(&2 pow 64) * &(bitval c) + &(val z):real =
                   &(val x) - &(val(word n:int64)) - &(bitval b) /\
                   read Xnn s = z) /\
                  (val x < val(word n:int64) + bitval b <=> c) /\
                  (val(word n:int64) + bitval b <= val x <=> ~c)`,
    MP_TAC pth_sbc THEN
    REPLICATE_TAC 3 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(fun th ->
    X_GEN_TAC `n:num` THEN MP_TAC(SPEC `word n:int64` th)) THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    REWRITE_TAC[WORD_ADD] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; ADD_ASSOC])
  and pth_sbc_r0 = prove
   (`!(s:S) Xnn (x:int64) b.
        read Xnn s = word_sub x (word(bitval b))
        ==> ?c z. (--(&2 pow 64) * &(bitval c) + &(val z):real =
                   &(val x) - &(bitval b) /\
                   read Xnn s = z) /\
                  (val x < 0 + bitval b <=> c) /\
                  (val x < bitval b <=> c) /\
                  (bitval b + 0 <= val x <=> ~c) /\
                  (bitval b <= val x <=> ~c)`,
    MP_TAC pth_sbc THEN
    REPLICATE_TAC 3 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `word 0:int64`) THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    REWRITE_TAC[WORD_ADD_0; VAL_WORD_0; ADD_CLAUSES] THEN
    REWRITE_TAC[REAL_SUB_RZERO; CONJ_ACI])
  and pth_adc_c0 = prove
   (`!(s:S) Xnn (x:int64) y.
        read Xnn s = word_add (word_add x y) (word 0)
        ==> ?c z. (&2 pow 64 * &(bitval c) + &(val z):real =
                   &(val x) + &(val y) /\
                   read Xnn s = z) /\
                  ((2 EXP 64 <= val x + val y + 0 <=> c) /\
                   (val x + val y + 0 < 2 EXP 64 <=> ~c) /\
                   (2 EXP 64 <= val x + val y + 0 <=> c) /\
                   (val x + val y + 0 < 2 EXP 64 <=> ~c))`,
    MP_TAC pth_adc THEN
    REPLICATE_TAC 4 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `F`) THEN
    REWRITE_TAC[WORD_ADD_0; VAL_WORD_0; REAL_ADD_LID; NOT_LE] THEN
    REWRITE_TAC[ADD_CLAUSES; BITVAL_CLAUSES; WORD_ADD_0; REAL_ADD_RID] THEN
    REWRITE_TAC[CONJ_ACI])
  and pth_add_r0 = prove
   (`!(s:S) Xnn (x:int64) b.
        read Xnn s = word_add x (word(bitval b))
        ==> ?c z. (&2 pow 64 * &(bitval c) + &(val z):real =
                   &(val x) + &(bitval b) /\
                   read Xnn s = z) /\
                  ((2 EXP 64 <= val x + bitval b) <=> c) /\
                  ((2 EXP 64 <= val x + 0 + bitval b) <=> c) /\
                  ((2 EXP 64 <= 0 + val x + bitval b) <=> c) /\
                  ((val x + bitval b < 2 EXP 64) <=> ~c) /\
                  ((val x + 0 + bitval b < 2 EXP 64) <=> ~c) /\
                  ((0 + val x + bitval b < 2 EXP 64) <=> ~c)`,
    MP_TAC pth_adc THEN
    REPLICATE_TAC 3 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `word 0:int64`) THEN
    REWRITE_TAC[WORD_ADD_0; VAL_WORD_0; REAL_ADD_LID; NOT_LE] THEN
    REWRITE_TAC[ADD_CLAUSES; CONJ_ACI])
  and pth_adc_c1 = prove
   (`!(s:S) Xnn (x:int64) y.
        read Xnn s = word_add (word_add x y) (word 1)
        ==> ?c z. (&2 pow 64 * &(bitval c) + &(val z):real =
                   &(val x) + &(val y) + &1 /\
                   read Xnn s = z) /\
                  ((2 EXP 64 <= val x + val y + 1 <=> c) /\
                   (val x + val y + 1 < 2 EXP 64 <=> ~c))`,
    MP_TAC pth_adc THEN
    REPLICATE_TAC 4 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `T`) THEN
    REWRITE_TAC[VAL_WORD_1; BITVAL_CLAUSES])
  and pth_adc_rn = prove
   (`!(s:S) Xnn (x:int64) n b.
        read Xnn s = word_add x (word(n + bitval b))
        ==> ?c z. (&2 pow 64 * &(bitval c) + &(val z):real =
                   &(val x) + &(val(word n:int64)) + &(bitval b) /\
                   read Xnn s = z) /\
                  ((2 EXP 64 <= val x + val(word n:int64) + bitval b) <=> c) /\
                  ((val x + val(word n:int64) + bitval b < 2 EXP 64) <=> ~c)`,
    MP_TAC pth_adc THEN
    REPLICATE_TAC 3 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(fun th ->
    X_GEN_TAC `n:num` THEN MP_TAC(SPEC `word n:int64` th)) THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    REWRITE_TAC[WORD_ADD] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; ADD_ASSOC])
  and pth_add = prove
   (`!(s:S) Xnn (x:int64) y.
        read Xnn s = word_add x y
        ==> ?c z. (&2 pow 64 * &(bitval c) + &(val z):real =
                   &(val x) + &(val y) /\
                   read Xnn s = z) /\
                  ((2 EXP 64 <= val x + val y) <=> c) /\
                  ((val x + val y < 2 EXP 64) <=> ~c)`,
    MP_TAC pth_adc THEN
    REPLICATE_TAC 4 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `F`) THEN
    REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; REAL_ADD_RID; WORD_ADD_0]) in
  let MATCH_MTH_TAC th =
    let th' = try MATCH_MP pth_mul_hi th with Failure _ ->
              try MATCH_MP pth_mul_lo th with Failure _ ->
              failwith "No matching accum theorem" in
    MP_TAC th'
  and MATCH_NTH_TAC th =
    let th' = try MATCH_MP pth_mul_hi2 th with Failure _ ->
              try MATCH_MP pth_mul_lo2 th with Failure _ ->
              failwith "No matching accum theorem" in
    MP_TAC th'
  and MATCH_LTH_TAC th =
    let th' = try MATCH_MP pth_mul_hil th with Failure _ ->
              try MATCH_MP pth_mul_hir th with Failure _ ->
              try MATCH_MP pth_mul_lol th with Failure _ ->
              try MATCH_MP pth_mul_lor th with Failure _ ->
              failwith "No matching accum theorem" in
    MP_TAC th'
  and MATCH_KTH_TAC th =
    let th' = try MATCH_MP pth_mul_hil2 th with Failure _ ->
              try MATCH_MP pth_mul_hir2 th with Failure _ ->
              try MATCH_MP pth_mul_lol2 th with Failure _ ->
              try MATCH_MP pth_mul_lor2 th with Failure _ ->
              failwith "No matching accum theorem" in
    MP_TAC th'
  and MATCH_ETH_TAC th =
    let th' = try MATCH_MP pth_extr th with Failure _ ->
              try MATCH_MP pth_ushr th with Failure _ ->
              failwith "No matching accum theorem" in
    MP_TAC th'
  and MATCH_PTH_TAC th =
    let th' = try MATCH_MP pth_adc th with Failure _ ->
              try MATCH_MP pth_adc_rn th with Failure _ ->
              try MATCH_MP pth_adc_c1 th with Failure _ ->
              try MATCH_MP pth_adc_c0 th with Failure _ ->
              try MATCH_MP pth_add_r0 th with Failure _ ->
              try MATCH_MP pth_sbc th with Failure _ ->
              try MATCH_MP pth_sbc_rn th with Failure _ ->
              try MATCH_MP pth_sbc_r0 th with Failure _ ->
              try MATCH_MP pth_add th with Failure _ ->
              try MATCH_MP pth_sub th with Failure _ ->
              failwith "No matching accum theorem" in
    MP_TAC th' in
  fun excls ->
    let filterpred t =
      match t with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),_)),_) ->
          mem c excls
      | _ -> false in
  fun s ->
    let matchfn t =
      patfn t &&
      let sv = rand(lhand t) in is_var sv && fst(dest_var sv) = s in
    FIRST_X_ASSUM(fun sth ->
     if filterpred(concl sth) then failwith "" else
     ((fun gl -> ((MATCH_MTH_TAC o check (matchfn o concl)) sth THEN
       DISCH_THEN(X_CHOOSE_THEN (mk_var("mulhi_"^s,int64_ty))
        (X_CHOOSE_THEN (mk_var("mullo_"^s,int64_ty)) MP_TAC)) THEN
       DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
        (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC))) gl) ORELSE

      (fun gl -> ((MATCH_NTH_TAC o check (matchfn o concl)) sth THEN
       DISCH_THEN(X_CHOOSE_THEN (mk_var("mulhi_"^s,int64_ty))
        (X_CHOOSE_THEN (mk_var("mullo_"^s,int64_ty)) MP_TAC)) THEN
       DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
        (REPEAT_TCL CONJUNCTS_THEN
          (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)))) gl) ORELSE

      (fun gl -> ((MATCH_LTH_TAC o check (matchfn o concl)) sth THEN
       ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN NO_TAC; ALL_TAC] THEN
       DISCH_THEN(X_CHOOSE_THEN (mk_var("mulhi_"^s,int64_ty))
        (X_CHOOSE_THEN (mk_var("mullo_"^s,int64_ty)) MP_TAC)) THEN
       DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
        (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC))) gl) ORELSE

      (fun gl -> ((MATCH_KTH_TAC o check (matchfn o concl)) sth THEN
       ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN NO_TAC; ALL_TAC] THEN
       DISCH_THEN(X_CHOOSE_THEN (mk_var("mulhi_"^s,int64_ty))
        (X_CHOOSE_THEN (mk_var("mullo_"^s,int64_ty)) MP_TAC)) THEN
       DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
        (REPEAT_TCL CONJUNCTS_THEN
          (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)))) gl) ORELSE

      (fun gl -> ((MATCH_ETH_TAC o check (matchfn o concl)) sth THEN
       ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN NO_TAC; ALL_TAC] THEN
       DISCH_THEN(X_CHOOSE_THEN (mk_var("mulhi_"^s,int64_ty))
        (X_CHOOSE_THEN (mk_var("mullo_"^s,int64_ty)) MP_TAC)) THEN
       CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_SUB_CONV)) THEN
       DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
        (REPEAT_TCL CONJUNCTS_THEN
          (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)))) gl) ORELSE

      (fun gl -> ((MATCH_PTH_TAC o check (matchfn o concl)) sth THEN
       CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_VAL_CONV)) THEN
       DISCH_THEN(X_CHOOSE_THEN (mk_var("carry_"^s,bool_ty))
        (X_CHOOSE_THEN (mk_var("sum_"^s,int64_ty)) MP_TAC)) THEN
       DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
        (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC))) gl) ORELSE

      (fun gl -> ((MATCH_PTH_TAC o
          MATCH_MP pth_zerotrig o check (matchfn o concl)) sth THEN
       CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_VAL_CONV)) THEN
       DISCH_THEN(X_CHOOSE_THEN (mk_var("carry_"^s,bool_ty))
        (X_CHOOSE_THEN (mk_var("sum_"^s,int64_ty)) MP_TAC)) THEN
       DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
        (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC))) gl)));;

let ACCUMULATE_ARITH_TAC = ACCUMULATEX_ARITH_TAC [];;
