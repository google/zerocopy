(* ========================================================================= *)
(* Calculation with rational-valued reals.                                   *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "real.ml";;

(* ------------------------------------------------------------------------- *)
(* Constant for decimal fractions written #xxx.yyy                           *)
(* ------------------------------------------------------------------------- *)

let DECIMAL = new_definition
  `DECIMAL x y = &x / &y`;;

(* ------------------------------------------------------------------------- *)
(* Various handy lemmas.                                                     *)
(* ------------------------------------------------------------------------- *)

let RAT_LEMMA1 = prove
 (`~(y1 = &0) /\ ~(y2 = &0) ==>
      ((x1 / y1) + (x2 / y2) = (x1 * y2 + x2 * y1) * inv(y1) * inv(y2))`,
  STRIP_TAC THEN REWRITE_TAC[real_div; REAL_ADD_RDISTRIB] THEN BINOP_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN ONCE_REWRITE_TAC
     [AC REAL_MUL_AC `a * b * c = (b * a) * c`];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN REWRITE_TAC[REAL_EQ_MUL_LCANCEL] THEN
  DISJ2_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_MUL_RINV THEN
  ASM_REWRITE_TAC[]);;

let RAT_LEMMA2 = prove
 (`&0 < y1 /\ &0 < y2 ==>
      ((x1 / y1) + (x2 / y2) = (x1 * y2 + x2 * y1) * inv(y1) * inv(y2))`,
  DISCH_TAC THEN MATCH_MP_TAC RAT_LEMMA1 THEN POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_LT_REFL]);;

let RAT_LEMMA3 = prove
 (`&0 < y1 /\ &0 < y2 ==>
      ((x1 / y1) - (x2 / y2) = (x1 * y2 - x2 * y1) * inv(y1) * inv(y2))`,
  DISCH_THEN(MP_TAC o GEN_ALL o MATCH_MP RAT_LEMMA2) THEN
  REWRITE_TAC[real_div] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[real_sub; GSYM REAL_MUL_LNEG]);;

let RAT_LEMMA4 = prove
 (`&0 < y1 /\ &0 < y2 ==> (x1 / y1 <= x2 / y2 <=> x1 * y2 <= x2 * y1)`,
  let lemma = prove
   (`&0 < y ==> (&0 <= x * y <=> &0 <= x)`,
    DISCH_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [SUBGOAL_THEN `&0 <= x * (y * inv y)` MP_TAC THENL
       [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `y * inv y = &1` (fun th ->
          REWRITE_TAC[th; REAL_MUL_RID]) THEN
        MATCH_MP_TAC REAL_MUL_RINV THEN
        UNDISCH_TAC `&0 < y` THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]) in
  ONCE_REWRITE_TAC[CONJ_SYM] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a <= b <=> &0 <= b - a`] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RAT_LEMMA3 th]) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `&0 <= (x2 * y1 - x1 * y2) * inv y2` THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN CONJ_TAC THEN
  MATCH_MP_TAC lemma THEN MATCH_MP_TAC REAL_LT_INV THEN
  ASM_REWRITE_TAC[]);;

let RAT_LEMMA5 = prove
 (`&0 < y1 /\ &0 < y2 ==> ((x1 / y1 = x2 / y2) <=> (x1 * y2 = x2 * y1))`,
  REPEAT DISCH_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  MATCH_MP_TAC(TAUT `(a <=> a') /\ (b <=> b') ==> (a /\ b <=> a' /\ b')`) THEN
  CONJ_TAC THEN MATCH_MP_TAC RAT_LEMMA4 THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Create trivial rational from integer or decimal, and postconvert back.    *)
(* ------------------------------------------------------------------------- *)

let REAL_INT_RAT_CONV =
  let pth = prove
   (`(&x = &x / &1) /\
     (--(&x) = --(&x) / &1) /\
     (DECIMAL x y = &x / &y) /\
     (--(DECIMAL x y) = --(&x) / &y)`,
    REWRITE_TAC[REAL_DIV_1; DECIMAL] THEN
    REWRITE_TAC[real_div; REAL_MUL_LNEG]) in
  TRY_CONV(GEN_REWRITE_CONV I [pth]);;

(* ------------------------------------------------------------------------- *)
(* Relational operations.                                                    *)
(* ------------------------------------------------------------------------- *)

let REAL_RAT_LE_CONV =
  let pth = prove
   (`&0 < y1 ==> &0 < y2 ==> (x1 / y1 <= x2 / y2 <=> x1 * y2 <= x2 * y1)`,
    REWRITE_TAC[IMP_IMP; RAT_LEMMA4])
  and x1 = `x1:real` and x2 = `x2:real`
  and y1 = `y1:real` and y2 = `y2:real`
  and dest_le = dest_binop `(<=)`
  and dest_div = dest_binop `(/)` in
  let RAW_REAL_RAT_LE_CONV tm =
    let l,r = dest_le tm in
    let lx,ly = dest_div l
    and rx,ry = dest_div r in
    let th0 = INST [lx,x1; ly,y1; rx,x2; ry,y2] pth in
    let th1 = funpow 2 (MP_CONV REAL_INT_LT_CONV) th0 in
    let th2 = (BINOP_CONV REAL_INT_MUL_CONV THENC REAL_INT_LE_CONV)
              (rand(concl th1)) in
    TRANS th1 th2 in
   BINOP_CONV REAL_INT_RAT_CONV THENC RAW_REAL_RAT_LE_CONV;;

let REAL_RAT_LT_CONV =
  let pth = prove
   (`&0 < y1 ==> &0 < y2 ==> (x1 / y1 < x2 / y2 <=> x1 * y2 < x2 * y1)`,
    REWRITE_TAC[IMP_IMP] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_NOT_LE] THEN
    SIMP_TAC[TAUT `(~a <=> ~b) <=> (a <=> b)`; RAT_LEMMA4])
  and x1 = `x1:real` and x2 = `x2:real`
  and y1 = `y1:real` and y2 = `y2:real`
  and dest_lt = dest_binop `(<)`
  and dest_div = dest_binop `(/)` in
  let RAW_REAL_RAT_LT_CONV tm =
    let l,r = dest_lt tm in
    let lx,ly = dest_div l
    and rx,ry = dest_div r in
    let th0 = INST [lx,x1; ly,y1; rx,x2; ry,y2] pth in
    let th1 = funpow 2 (MP_CONV REAL_INT_LT_CONV) th0 in
    let th2 = (BINOP_CONV REAL_INT_MUL_CONV THENC REAL_INT_LT_CONV)
              (rand(concl th1)) in
    TRANS th1 th2 in
   BINOP_CONV REAL_INT_RAT_CONV THENC RAW_REAL_RAT_LT_CONV;;

let REAL_RAT_GE_CONV =
  GEN_REWRITE_CONV I [real_ge] THENC REAL_RAT_LE_CONV;;

let REAL_RAT_GT_CONV =
  GEN_REWRITE_CONV I [real_gt] THENC REAL_RAT_LT_CONV;;

let REAL_RAT_EQ_CONV =
  let pth = prove
   (`&0 < y1 ==> &0 < y2 ==> ((x1 / y1 = x2 / y2) <=> (x1 * y2 = x2 * y1))`,
    REWRITE_TAC[IMP_IMP; RAT_LEMMA5])
  and x1 = `x1:real` and x2 = `x2:real`
  and y1 = `y1:real` and y2 = `y2:real`
  and dest_eq = dest_binop `(=) :real->real->bool`
  and dest_div = dest_binop `(/)` in
  let RAW_REAL_RAT_EQ_CONV tm =
    let l,r = dest_eq tm in
    let lx,ly = dest_div l
    and rx,ry = dest_div r in
    let th0 = INST [lx,x1; ly,y1; rx,x2; ry,y2] pth in
    let th1 = funpow 2 (MP_CONV REAL_INT_LT_CONV) th0 in
    let th2 = (BINOP_CONV REAL_INT_MUL_CONV THENC REAL_INT_EQ_CONV)
              (rand(concl th1)) in
    TRANS th1 th2 in
   BINOP_CONV REAL_INT_RAT_CONV THENC RAW_REAL_RAT_EQ_CONV;;

let REAL_RAT_SGN_CONV =
  GEN_REWRITE_CONV I [real_sgn] THENC
  RATOR_CONV(LAND_CONV REAL_RAT_LT_CONV) THENC
  (GEN_REWRITE_CONV I [CONJUNCT1(SPEC_ALL COND_CLAUSES)] ORELSEC
   (GEN_REWRITE_CONV I [CONJUNCT2(SPEC_ALL COND_CLAUSES)] THENC
    RATOR_CONV(LAND_CONV REAL_RAT_LT_CONV) THENC
    GEN_REWRITE_CONV I [COND_CLAUSES]));;

(* ------------------------------------------------------------------------- *)
(* The unary operations; all easy.                                           *)
(* ------------------------------------------------------------------------- *)

let REAL_RAT_NEG_CONV =
  let pth = prove
   (`(--(&0) = &0) /\
     (--(--(&n)) = &n) /\
     (--(&m / &n) = --(&m) / &n) /\
     (--(--(&m) / &n) = &m / &n) /\
     (--(DECIMAL m n) = --(&m) / &n)`,
    REWRITE_TAC[real_div; REAL_INV_NEG; REAL_MUL_LNEG; REAL_NEG_NEG;
     REAL_NEG_0; DECIMAL])
  and ptm = `(--)` in
  let conv1 = GEN_REWRITE_CONV I [pth] in
  fun tm -> try conv1 tm
            with Failure _ -> try
                let l,r = dest_comb tm in
                if l = ptm && is_realintconst r && dest_realintconst r >/ num_0
                then REFL tm
                else fail()
            with Failure _ -> failwith "REAL_RAT_NEG_CONV";;

let REAL_RAT_ABS_CONV =
  let pth = prove
   (`(abs(&n) = &n) /\
     (abs(--(&n)) = &n) /\
     (abs(&m / &n) = &m / &n) /\
     (abs(--(&m) / &n) = &m / &n) /\
     (abs(DECIMAL m n) = &m / &n) /\
     (abs(--(DECIMAL m n)) = &m / &n)`,
    REWRITE_TAC[DECIMAL; REAL_ABS_DIV; REAL_ABS_NEG; REAL_ABS_NUM]) in
  GEN_REWRITE_CONV I [pth];;

let REAL_RAT_INV_CONV =
  let pth1 = prove
   (`(inv(&0) = &0) /\
     (inv(&1) = &1) /\
     (inv(-- &1) = --(&1)) /\
     (inv(&1 / &n) = &n) /\
     (inv(-- &1 / &n) = -- &n)`,
    REWRITE_TAC[REAL_INV_0; REAL_INV_1; REAL_INV_NEG;
                REAL_INV_DIV; REAL_DIV_1] THEN
    REWRITE_TAC[real_div; REAL_INV_NEG; REAL_MUL_RNEG; REAL_INV_1;
                REAL_MUL_RID])
  and pth2 = prove
   (`(inv(&n) = &1 / &n) /\
     (inv(--(&n)) = --(&1) / &n) /\
     (inv(&m / &n) = &n / &m) /\
     (inv(--(&m) / &n) = --(&n) / &m) /\
     (inv(DECIMAL m n) = &n / &m) /\
     (inv(--(DECIMAL m n)) = --(&n) / &m)`,
    REWRITE_TAC[DECIMAL; REAL_INV_DIV] THEN
    REWRITE_TAC[REAL_INV_NEG; real_div; REAL_MUL_RNEG; REAL_MUL_AC;
      REAL_MUL_LID; REAL_MUL_LNEG; REAL_INV_MUL; REAL_INV_INV]) in
  GEN_REWRITE_CONV I [pth1] ORELSEC
  GEN_REWRITE_CONV I [pth2];;

(* ------------------------------------------------------------------------- *)
(* Addition.                                                                 *)
(* ------------------------------------------------------------------------- *)

let REAL_RAT_ADD_CONV =
  let pth = prove
   (`&0 < y1 ==> &0 < y2 ==> &0 < y3 ==>
     ((x1 * y2 + x2 * y1) * y3 = x3 * y1 * y2)
     ==> (x1 / y1 + x2 / y2 = x3 / y3)`,
    REPEAT DISCH_TAC THEN
    MP_TAC RAT_LEMMA2 THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM REAL_INV_MUL; GSYM real_div] THEN
    SUBGOAL_THEN `&0 < y1 * y2 /\ &0 < y3` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(fun th -> ASM_REWRITE_TAC[MATCH_MP RAT_LEMMA5 th])])
  and dest_divop = dest_binop `(/)`
  and dest_addop = dest_binop `(+)`
  and x1 = `x1:real` and x2 = `x2:real` and x3 = `x3:real`
  and y1 = `y1:real` and y2 = `y2:real` and y3 = `y3:real` in
  let RAW_REAL_RAT_ADD_CONV tm =
    let r1,r2 = dest_addop tm in
    let x1',y1' = dest_divop r1
    and x2',y2' = dest_divop r2 in
    let x1n = dest_realintconst x1' and y1n = dest_realintconst y1'
    and x2n = dest_realintconst x2' and y2n = dest_realintconst y2' in
    let x3n = x1n */ y2n +/ x2n */ y1n
    and y3n = y1n */ y2n in
    let d = gcd_num x3n y3n in
    let x3n' = quo_num x3n d and y3n' = quo_num y3n d in
    let x3n'',y3n'' = if y3n' >/ num 0 then x3n',y3n'
                      else minus_num x3n',minus_num y3n' in
    let x3' = mk_realintconst x3n'' and y3' = mk_realintconst y3n'' in
    let th0 = INST [x1',x1; y1',y1; x2',x2; y2',y2; x3',x3; y3',y3] pth in
    let th1 = funpow 3 (MP_CONV REAL_INT_LT_CONV) th0 in
    let tm2,tm3 = dest_eq(fst(dest_imp(concl th1))) in
    let th2 = (LAND_CONV (BINOP_CONV REAL_INT_MUL_CONV THENC
                          REAL_INT_ADD_CONV) THENC
               REAL_INT_MUL_CONV) tm2
    and th3 = (RAND_CONV REAL_INT_MUL_CONV THENC REAL_INT_MUL_CONV) tm3 in
    MP th1 (TRANS th2 (SYM th3)) in
   BINOP_CONV REAL_INT_RAT_CONV THENC
   RAW_REAL_RAT_ADD_CONV THENC TRY_CONV(GEN_REWRITE_CONV I [REAL_DIV_1]);;

(* ------------------------------------------------------------------------- *)
(* Subtraction.                                                              *)
(* ------------------------------------------------------------------------- *)

let REAL_RAT_SUB_CONV =
  let pth = prove
   (`x - y = x + --y`,
    REWRITE_TAC[real_sub]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV REAL_RAT_NEG_CONV THENC REAL_RAT_ADD_CONV;;

(* ------------------------------------------------------------------------- *)
(* Multiplication.                                                           *)
(* ------------------------------------------------------------------------- *)

let REAL_RAT_MUL_CONV =
  let pth_nocancel = prove
   (`(x1 / y1) * (x2 / y2) = (x1 * x2) / (y1 * y2)`,
    REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_AC])
  and pth_cancel = prove
   (`~(d1 = &0) /\ ~(d2 = &0) /\
     (d1 * u1 = x1) /\ (d2 * u2 = x2) /\
     (d2 * v1 = y1) /\ (d1 * v2 = y2)
     ==> ((x1 / y1) * (x2 / y2) = (u1 * u2) / (v1 * v2))`,
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
    ASM_REWRITE_TAC[real_div; REAL_INV_MUL] THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC
     `((d1 * u1) * (id2 * iv1)) * ((d2 * u2) * id1 * iv2) =
      (u1 * u2) * (iv1 * iv2) * (id2 * d2) * (id1 * d1)`] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_RID])
  and dest_divop = dest_binop `(/)`
  and dest_mulop = dest_binop `(*)`
  and x1 = `x1:real` and x2 = `x2:real`
  and y1 = `y1:real` and y2 = `y2:real`
  and u1 = `u1:real` and u2 = `u2:real`
  and v1 = `v1:real` and v2 = `v2:real`
  and d1 = `d1:real` and d2 = `d2:real` in
  let RAW_REAL_RAT_MUL_CONV tm =
    let r1,r2 = dest_mulop tm in
    let x1',y1' = dest_divop r1
    and x2',y2' = dest_divop r2 in
    let x1n = dest_realintconst x1' and y1n = dest_realintconst y1'
    and x2n = dest_realintconst x2' and y2n = dest_realintconst y2' in
    let d1n = gcd_num x1n y2n
    and d2n = gcd_num x2n y1n in
    if d1n =/ num_1 && d2n =/ num_1 then
      let th0 = INST [x1',x1; y1',y1; x2',x2; y2',y2] pth_nocancel in
      let th1 = BINOP_CONV REAL_INT_MUL_CONV (rand(concl th0)) in
      TRANS th0 th1
    else
      let u1n = quo_num x1n d1n
      and u2n = quo_num x2n d2n
      and v1n = quo_num y1n d2n
      and v2n = quo_num y2n d1n in
      let u1' = mk_realintconst u1n
      and u2' = mk_realintconst u2n
      and v1' = mk_realintconst v1n
      and v2' = mk_realintconst v2n
      and d1' = mk_realintconst d1n
      and d2' = mk_realintconst d2n in
      let th0 = INST [x1',x1; y1',y1; x2',x2; y2',y2;
                      u1',u1; v1',v1; u2',u2; v2',v2; d1',d1; d2',d2]
                     pth_cancel in
      let th1 = EQT_ELIM(REAL_INT_REDUCE_CONV(lhand(concl th0))) in
      let th2 = MP th0 th1 in
      let th3 = BINOP_CONV REAL_INT_MUL_CONV (rand(concl th2)) in
      TRANS th2 th3 in
   BINOP_CONV REAL_INT_RAT_CONV THENC
   RAW_REAL_RAT_MUL_CONV THENC TRY_CONV(GEN_REWRITE_CONV I [REAL_DIV_1]);;

(* ------------------------------------------------------------------------- *)
(* Division.                                                                 *)
(* ------------------------------------------------------------------------- *)

let REAL_RAT_DIV_CONV =
  let pth = prove
   (`x / y = x * inv(y)`,
    REWRITE_TAC[real_div]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV REAL_RAT_INV_CONV THENC REAL_RAT_MUL_CONV;;

(* ------------------------------------------------------------------------- *)
(* Powers.                                                                   *)
(* ------------------------------------------------------------------------- *)

let REAL_RAT_POW_CONV =
  let pth = prove
   (`(x / y) pow n = (x pow n) / (y pow n)`,
    REWRITE_TAC[REAL_POW_DIV]) in
  REAL_INT_POW_CONV ORELSEC
  (LAND_CONV REAL_INT_RAT_CONV THENC
   GEN_REWRITE_CONV I [pth] THENC
   BINOP_CONV REAL_INT_POW_CONV);;

(* ------------------------------------------------------------------------- *)
(* Max and min.                                                              *)
(* ------------------------------------------------------------------------- *)

let REAL_RAT_MAX_CONV =
  REWR_CONV real_max THENC
  RATOR_CONV(RATOR_CONV(RAND_CONV REAL_RAT_LE_CONV)) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES];;

let REAL_RAT_MIN_CONV =
  REWR_CONV real_min THENC
  RATOR_CONV(RATOR_CONV(RAND_CONV REAL_RAT_LE_CONV)) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES];;

(* ------------------------------------------------------------------------- *)
(* Everything.                                                               *)
(* ------------------------------------------------------------------------- *)

let real_rat_red_conv_list =
  [`x <= y`,REAL_RAT_LE_CONV;
   `x < y`,REAL_RAT_LT_CONV;
   `x >= y`,REAL_RAT_GE_CONV;
   `x > y`,REAL_RAT_GT_CONV;
   `x:real = y`,REAL_RAT_EQ_CONV;
   `--x`,CHANGED_CONV REAL_RAT_NEG_CONV;
   `real_sgn(x)`,REAL_RAT_SGN_CONV;
   `abs(x)`,REAL_RAT_ABS_CONV;
   `inv(x)`,REAL_RAT_INV_CONV;
   `x + y`,REAL_RAT_ADD_CONV;
   `x - y`,REAL_RAT_SUB_CONV;
   `x * y`,REAL_RAT_MUL_CONV;
   `x / y`,CHANGED_CONV REAL_RAT_DIV_CONV;
   `x pow n`,REAL_RAT_POW_CONV;
   `max x y`,REAL_RAT_MAX_CONV;
   `min x y`,REAL_RAT_MIN_CONV];;

let REAL_RAT_RED_CONV =
  let gconv_net = itlist (uncurry net_of_conv) real_rat_red_conv_list
    (basic_net()) in
  REWRITES_CONV gconv_net;;

let REAL_RAT_REDUCE_CONV = DEPTH_CONV REAL_RAT_RED_CONV;;

let real_rat_compute_add_convs =
  let convlist = map (fun pat,the_conv ->
    let c,args = strip_comb pat in (c,length args,the_conv))
    real_rat_red_conv_list in
  fun (compset:Compute.compset) ->
    itlist (fun newc () -> Compute.add_conv newc compset) convlist ();;

let REAL_RAT_COMPUTE_CONV =
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  real_rat_compute_add_convs cs;
  Compute.WEAK_CBV_CONV cs;;

(* ------------------------------------------------------------------------- *)
(* Real normalizer dealing with rational constants.                          *)
(* ------------------------------------------------------------------------- *)

let REAL_POLY_NEG_CONV,REAL_POLY_ADD_CONV,REAL_POLY_SUB_CONV,
    REAL_POLY_MUL_CONV,REAL_POLY_POW_CONV,REAL_POLY_CONV =
  SEMIRING_NORMALIZERS_CONV REAL_POLY_CLAUSES REAL_POLY_NEG_CLAUSES
   (is_ratconst,
    REAL_RAT_ADD_CONV,REAL_RAT_MUL_CONV,REAL_RAT_POW_CONV)
   (<);;

(* ------------------------------------------------------------------------- *)
(* Extend normalizer to handle "inv" and division by rational constants, and *)
(* normalize inside nested "max", "min" and "abs" terms.                     *)
(* ------------------------------------------------------------------------- *)

let REAL_POLY_CONV =
  let neg_tm = `(--):real->real`
  and inv_tm = `inv:real->real`
  and add_tm = `(+):real->real->real`
  and sub_tm = `(-):real->real->real`
  and mul_tm = `(*):real->real->real`
  and div_tm = `(/):real->real->real`
  and pow_tm = `(pow):real->num->real`
  and abs_tm = `abs:real->real`
  and max_tm = `max:real->real->real`
  and min_tm = `min:real->real->real`
  and div_conv = REWR_CONV real_div in
  let rec REAL_POLY_CONV tm =
    if not(is_comb tm) || is_ratconst tm then REFL tm else
    let lop,r = dest_comb tm in
    if lop = neg_tm then
      let th1 = AP_TERM lop (REAL_POLY_CONV r) in
      TRANS th1 (REAL_POLY_NEG_CONV (rand(concl th1)))
    else if lop = inv_tm then
      let th1 = AP_TERM lop (REAL_POLY_CONV r) in
      TRANS th1 (TRY_CONV REAL_RAT_INV_CONV (rand(concl th1)))
    else if lop = abs_tm then
      AP_TERM lop (REAL_POLY_CONV r)
    else if not(is_comb lop) then REFL tm else
    let op,l = dest_comb lop in
    if op = pow_tm then
      let th1 = AP_THM (AP_TERM op (REAL_POLY_CONV l)) r in
      TRANS th1 (TRY_CONV REAL_POLY_POW_CONV (rand(concl th1)))
    else if op = add_tm || op = mul_tm || op = sub_tm then
      let th1 = MK_COMB(AP_TERM op (REAL_POLY_CONV l),
                        REAL_POLY_CONV r) in
      let fn = if op = add_tm then REAL_POLY_ADD_CONV
               else if op = mul_tm then REAL_POLY_MUL_CONV
               else REAL_POLY_SUB_CONV in
      TRANS th1 (fn (rand(concl th1)))
    else if op = div_tm then
      let th1 = div_conv tm in
      TRANS th1 (REAL_POLY_CONV (rand(concl th1)))
    else if op = min_tm || op = max_tm then
      MK_COMB(AP_TERM op (REAL_POLY_CONV l),REAL_POLY_CONV r)
    else REFL tm in
  REAL_POLY_CONV;;

(* ------------------------------------------------------------------------- *)
(* Basic ring and ideal conversions.                                         *)
(* ------------------------------------------------------------------------- *)

let REAL_RING,real_ideal_cofactors =
  let REAL_INTEGRAL = prove
   (`(!x. &0 * x = &0) /\
     (!x y z. (x + y = x + z) <=> (y = z)) /\
     (!w x y z. (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))`,
    REWRITE_TAC[MULT_CLAUSES; EQ_ADD_LCANCEL] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ;
                GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
    REWRITE_TAC[GSYM REAL_ENTIRE] THEN REAL_ARITH_TAC)
  and REAL_RABINOWITSCH = prove
   (`!x y:real. ~(x = y) <=> ?z. (x - y) * z = &1`,
    REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_SUB_0] THEN
    MESON_TAC[REAL_MUL_RINV; REAL_MUL_LZERO; REAL_ARITH `~(&1 = &0)`])
  and init = GEN_REWRITE_CONV ONCE_DEPTH_CONV [DECIMAL]
  and real_ty = `:real` in
  let pure,ideal =
    RING_AND_IDEAL_CONV
        (rat_of_term,term_of_rat,REAL_RAT_EQ_CONV,
         `(--):real->real`,`(+):real->real->real`,`(-):real->real->real`,
         `(inv):real->real`,`(*):real->real->real`,`(/):real->real->real`,
         `(pow):real->num->real`,
         REAL_INTEGRAL,REAL_RABINOWITSCH,REAL_POLY_CONV) in
  (fun tm -> let th = init tm in EQ_MP (SYM th) (pure(rand(concl th)))),
  (fun tms tm -> if forall (fun t -> type_of t = real_ty) (tm::tms)
                 then ideal tms tm
                 else failwith
                   "real_ideal_cofactors: not all terms have type :real");;

(* ------------------------------------------------------------------------- *)
(* Conversion for ideal membership.                                          *)
(* ------------------------------------------------------------------------- *)

let REAL_IDEAL_CONV =
  let mk_add = mk_binop `( + ):real->real->real`
  and mk_mul = mk_binop `( * ):real->real->real` in
  fun tms tm ->
    let cfs = real_ideal_cofactors tms tm in
    let tm' = end_itlist mk_add (map2 mk_mul cfs tms) in
    let th = REAL_POLY_CONV tm and th' = REAL_POLY_CONV tm' in
    TRANS th (SYM th');;

(* ------------------------------------------------------------------------- *)
(* Further specialize GEN_REAL_ARITH and REAL_ARITH (final versions).        *)
(* ------------------------------------------------------------------------- *)

let GEN_REAL_ARITH PROVER =
  GEN_REAL_ARITH
   (term_of_rat,
    REAL_RAT_EQ_CONV,REAL_RAT_GE_CONV,REAL_RAT_GT_CONV,
    REAL_POLY_CONV,REAL_POLY_NEG_CONV,REAL_POLY_ADD_CONV,REAL_POLY_MUL_CONV,
    PROVER);;

let REAL_ARITH =
  let init = GEN_REWRITE_CONV ONCE_DEPTH_CONV [DECIMAL]
  and pure = GEN_REAL_ARITH REAL_LINEAR_PROVER in
  fun tm ->
    try
      let th = init tm in EQ_MP (SYM th) (pure(rand(concl th)))
    with Failure m ->
      failwith ("REAL_ARITH `" ^ (string_of_term tm) ^ "`: " ^ m);;

let REAL_ARITH_TAC = CONV_TAC REAL_ARITH;;

let ASM_REAL_ARITH_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (not o is_forall o concl))) THEN
  REAL_ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* A few handy equivalential forms of transitivity.                          *)
(* ------------------------------------------------------------------------- *)

let REAL_LE_TRANS_LE = prove
 (`!x y:real. x <= y <=> (!z. y <= z ==> x <= z)`,
  MESON_TAC[REAL_LE_TRANS; REAL_LE_REFL]);;

let REAL_LE_TRANS_LTE = prove
 (`!x y:real. x <= y <=> (!z. y < z ==> x <= z)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y + (x - y) / &2`) THEN REAL_ARITH_TAC);;

let REAL_LE_TRANS_LT = prove
 (`!x y:real. x <= y <=> (!z. y < z ==> x < z)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y + (x - y) / &2`) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A simple "field" rule.                                                    *)
(* ------------------------------------------------------------------------- *)

let REAL_FIELD =
  let norm_net =
    itlist (net_of_thm false o SPEC_ALL)
     [FORALL_SIMP; EXISTS_SIMP; real_div; REAL_INV_INV; REAL_INV_MUL;
      REAL_POW_ADD]
    (net_of_conv
      `inv((x:real) pow n)`
      (REWR_CONV(GSYM REAL_POW_INV) o check (is_numeral o rand o rand))
      empty_net)
  and easy_nz_conv =
    LAND_CONV
     (GEN_REWRITE_CONV TRY_CONV [MESON[REAL_POW_EQ_0; REAL_OF_NUM_EQ]
       `~(x pow n = &0) <=>
        ~((x:real) = &0) \/ (&n = &0) \/ ~(x pow n = &0)`]) THENC
    TRY_CONV(LAND_CONV REAL_RAT_REDUCE_CONV THENC
             GEN_REWRITE_CONV I [TAUT `(T ==> p) <=> p`]) in
  let prenex_conv =
    TOP_DEPTH_CONV BETA_CONV THENC
    NUM_REDUCE_CONV THENC
    TOP_DEPTH_CONV(REWRITES_CONV norm_net) THENC
    NNFC_CONV THENC DEPTH_BINOP_CONV `(/\)` CONDS_CELIM_CONV THENC
    PRENEX_CONV THENC
    ONCE_REWRITE_CONV[REAL_ARITH `x < y <=> x < y /\ ~(x = y)`]
  and setup_conv = NNF_CONV THENC WEAK_CNF_CONV THENC CONJ_CANON_CONV
  and core_rule t = try REAL_RING t with Failure _ -> REAL_ARITH t
  and is_inv =
    let inv_tm = `inv:real->real`
    and is_div = is_binop `(/):real->real->real` in
    fun tm -> (is_div tm || (is_comb tm && rator tm = inv_tm)) &&
              not(is_ratconst(rand tm)) in
  let BASIC_REAL_FIELD tm =
    let is_freeinv t = is_inv t && free_in t tm in
    let itms = setify(map rand (find_terms is_freeinv tm)) in
    let hyps = map
     (fun t -> CONV_RULE easy_nz_conv (SPEC t REAL_MUL_RINV)) itms in
    let tm' = itlist (fun th t -> mk_imp(concl th,t)) hyps tm in
    let th1 = setup_conv tm' in
    let cjs = conjuncts(rand(concl th1)) in
    let ths = map core_rule cjs in
    let th2 = EQ_MP (SYM th1) (end_itlist CONJ ths) in
    rev_itlist (C MP) hyps th2 in
  fun tm ->
    let th0 = prenex_conv tm in
    let tm0 = rand(concl th0) in
    let avs,bod = strip_forall tm0 in
    let th1 = setup_conv bod in
    let ths = map BASIC_REAL_FIELD (conjuncts(rand(concl th1))) in
    EQ_MP (SYM th0) (GENL avs (EQ_MP (SYM th1) (end_itlist CONJ ths)));;

(* ------------------------------------------------------------------------- *)
(* Useful monotone mappings between R and (-1,1)                             *)
(* ------------------------------------------------------------------------- *)

let REAL_SHRINK_RANGE = prove
 (`!x. abs(x / (&1 + abs x)) < &1`,
  GEN_TAC THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ARITH `abs(&1 + abs x) = &1 + abs x`] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &1 + abs x`] THEN
  REAL_ARITH_TAC);;

let REAL_SHRINK_LT = prove
 (`!x y. x / (&1 + abs x) < y / (&1 + abs y) <=> x < y`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH
   `(&0 < x' <=> &0 < x) /\ (&0 < y' <=> &0 < y) /\
    (abs x' < abs y' <=> abs x < abs y) /\ (abs y' < abs x' <=> abs y < abs x)
    ==> (x' < y' <=> x < y)`) THEN
  SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < &1 + abs x`; REAL_MUL_LZERO] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`y:real`; `x:real`] THEN
  REWRITE_TAC[MESON[] `(!x y. P x y /\ P y x) <=> (!x y. P x y)`] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ARITH `abs(&1 + abs x) = &1 + abs x`] THEN
  SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < &1 + abs x`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a / b * c:real = (a * c) / b`] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &1 + abs x`] THEN
  REAL_ARITH_TAC);;

let REAL_SHRINK_LE = prove
 (`!x y. x / (&1 + abs x) <= y / (&1 + abs y) <=> x <= y`,
  REWRITE_TAC[GSYM REAL_NOT_LT; REAL_SHRINK_LT]);;

let REAL_SHRINK_EQ = prove
 (`!x y. x / (&1 + abs x) = y / (&1 + abs y) <=> x = y`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM; REAL_SHRINK_LE]);;

let REAL_SHRINK_GALOIS = prove
 (`!x y. x / (&1 + abs x) = y <=> abs y < &1 /\ y / (&1 - abs y) = x`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[REAL_SHRINK_RANGE] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `abs(&1 + abs x) = &1 + abs x`;
               REAL_ARITH `abs y < &1 ==> abs(&1 - abs y) = &1 - abs y`] THEN
  MATCH_MP_TAC(REAL_ARITH `x * inv y * inv z = x * &1 ==> x / y / z = x`) THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC(REAL_FIELD `x * y = &1 ==> inv x * inv y = &1`) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let REAL_GROW_SHRINK = prove
 (`!x. x / (&1 + abs x) / (&1 - abs(x / (&1 + abs x))) = x`,
  MESON_TAC[REAL_SHRINK_GALOIS; REAL_SHRINK_RANGE]);;

let REAL_SHRINK_GROW_EQ = prove
 (`!x. x / (&1 - abs x) / (&1 + abs(x / (&1 - abs x))) = x <=> abs x < &1`,
  MESON_TAC[REAL_SHRINK_GALOIS; REAL_SHRINK_RANGE]);;

let REAL_SHRINK_GROW = prove
 (`!x. abs x < &1
       ==> x / (&1 - abs x) / (&1 + abs(x / (&1 - abs x))) = x`,
  REWRITE_TAC[REAL_SHRINK_GROW_EQ]);;
