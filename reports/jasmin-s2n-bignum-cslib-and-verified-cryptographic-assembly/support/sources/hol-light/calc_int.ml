(* ========================================================================= *)
(* Calculation with integer-valued reals.                                    *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "realax.ml";;

(* ------------------------------------------------------------------------- *)
(* Syntax operations on integer constants of type ":real".                   *)
(* ------------------------------------------------------------------------- *)

let is_realintconst tm =
  match tm with
    Comb(Const("real_of_num",_),n) -> is_numeral n
  | Comb(Const("real_neg",_),Comb(Const("real_of_num",_),n)) ->
      is_numeral n && not(dest_numeral n =/ num_0)
  | _ -> false;;

let dest_realintconst tm =
  match tm with
    Comb(Const("real_of_num",_),n) -> dest_numeral n
  | Comb(Const("real_neg",_),Comb(Const("real_of_num",_),n)) ->
        let nn = dest_numeral n in
        if nn <>/ num_0 then minus_num(dest_numeral n)
        else failwith "dest_realintconst"
  | _ -> failwith "dest_realintconst";;

let mk_realintconst =
  let cast_tm = `real_of_num` and neg_tm = `(--)` in
  let mk_numconst n = mk_comb(cast_tm,mk_numeral n) in
  fun x -> if x </ num_0 then mk_comb(neg_tm,mk_numconst(minus_num x))
           else mk_numconst x;;

let is_ratconst tm =
  match tm with
    Comb(Comb(Const("real_div",_),p),q) ->
        is_realintconst p && is_realintconst q &&
        (let m = dest_realintconst p and n = dest_realintconst q in
         n >/ num_1 && gcd_num m n =/ num_1)
  | _ -> is_realintconst tm;;

let rat_of_term tm =
  match tm with
    Comb(Comb(Const("real_div",_),p),q) ->
        let m = dest_realintconst p and n = dest_realintconst q in
        if n >/ num_1 && gcd_num m n =/ num_1 then m // n
        else failwith "rat_of_term"
  | _ -> dest_realintconst tm;;

let term_of_rat =
  let div_tm = `(/)` in
  fun x ->
    let p,q = numdom x in
    let ptm = mk_realintconst p in
    if q =/ num_1 then ptm
    else mk_comb(mk_comb(div_tm,ptm),mk_realintconst q);;

(* ------------------------------------------------------------------------- *)
(* Some elementary "bootstrapping" lemmas we need below.                     *)
(* ------------------------------------------------------------------------- *)

let REAL_ADD_AC = prove
 (`(m + n = n + m) /\
   ((m + n) + p = m + (n + p)) /\
   (m + (n + p) = n + (m + p))`,
  MESON_TAC[REAL_ADD_ASSOC; REAL_ADD_SYM]);;

let REAL_ADD_RINV = prove
 (`!x. x + --x = &0`,
  MESON_TAC[REAL_ADD_SYM; REAL_ADD_LINV]);;

let REAL_EQ_ADD_LCANCEL = prove
 (`!x y z. (x + y = x + z) <=> (y = z)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(MP_TAC o AP_TERM `(+) (--x)`) THEN
  REWRITE_TAC[REAL_ADD_ASSOC; REAL_ADD_LINV; REAL_ADD_LID]);;

let REAL_EQ_ADD_RCANCEL = prove
 (`!x y z. (x + z = y + z) <=> (x = y)`,
  MESON_TAC[REAL_ADD_SYM; REAL_EQ_ADD_LCANCEL]);;

let REAL_MUL_RZERO = prove
 (`!x. x * &0 = &0`,
  MESON_TAC[REAL_EQ_ADD_RCANCEL; REAL_ADD_LDISTRIB; REAL_ADD_LID]);;

let REAL_MUL_LZERO = prove
 (`!x. &0 * x = &0`,
  MESON_TAC[REAL_MUL_SYM; REAL_MUL_RZERO]);;

let REAL_NEG_NEG = prove
 (`!x. --(--x) = x`,
  MESON_TAC
   [REAL_EQ_ADD_RCANCEL; REAL_ADD_LINV; REAL_ADD_SYM; REAL_ADD_LINV]);;

let REAL_MUL_RNEG = prove
 (`!x y. x * (--y) = -- (x * y)`,
  MESON_TAC[REAL_EQ_ADD_RCANCEL; REAL_ADD_LDISTRIB; REAL_ADD_LINV;
            REAL_MUL_RZERO]);;

let REAL_MUL_LNEG = prove
 (`!x y. (--x) * y = -- (x * y)`,
  MESON_TAC[REAL_MUL_SYM; REAL_MUL_RNEG]);;

let REAL_NEG_ADD = prove
 (`!x y. --(x + y) = --x + --y`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL REAL_EQ_ADD_RCANCEL)))) THEN
  EXISTS_TAC `x + y` THEN REWRITE_TAC[REAL_ADD_LINV] THEN
  ONCE_REWRITE_TAC[AC REAL_ADD_AC `(a + b) + (c + d) = (a + c) + (b + d)`] THEN
  REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_LID]);;

let REAL_ADD_RID = prove
 (`!x. x + &0 = x`,
  MESON_TAC[REAL_ADD_SYM; REAL_ADD_LID]);;

let REAL_NEG_0 = prove
 (`--(&0) = &0`,
  MESON_TAC[REAL_ADD_LINV; REAL_ADD_RID]);;

let REAL_LE_LNEG = prove
 (`!x y. --x <= y <=> &0 <= x + y`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LADD_IMP) THENL
   [DISCH_THEN(MP_TAC o SPEC `x:real`) THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_ADD_LINV];
    DISCH_THEN(MP_TAC o SPEC `--x`) THEN
    REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_ASSOC; REAL_ADD_LID;
        ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_ADD_LID]]);;

let REAL_LE_NEG2 = prove
 (`!x y. --x <= --y <=> y <= x`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM REAL_NEG_NEG] THEN
  REWRITE_TAC[REAL_LE_LNEG] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_ADD_SYM);;

let REAL_LE_RNEG = prove
 (`!x y. x <= --y <=> x + y <= &0`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM REAL_NEG_NEG] THEN
  REWRITE_TAC[REAL_LE_LNEG; GSYM REAL_NEG_ADD] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_LE_NEG2] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM REAL_ADD_LINV] THEN
  REWRITE_TAC[REAL_NEG_ADD; REAL_NEG_NEG] THEN
  MATCH_ACCEPT_TAC REAL_ADD_SYM);;

let REAL_OF_NUM_POW = prove
 (`!x n. (&x) pow n = &(x EXP n)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[real_pow; EXP; REAL_OF_NUM_MUL]);;

let REAL_POW_NEG = prove
 (`!x n. (--x) pow n = if EVEN n then x pow n else --(x pow n)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[real_pow; EVEN] THEN
  ASM_CASES_TAC `EVEN n` THEN
  ASM_REWRITE_TAC[REAL_MUL_RNEG; REAL_MUL_LNEG; REAL_NEG_NEG]);;

let REAL_ABS_NUM = prove
 (`!n. abs(&n) = &n`,
  REWRITE_TAC[real_abs; REAL_OF_NUM_LE; LE_0]);;

let REAL_ABS_NEG = prove
 (`!x. abs(--x) = abs x`,
  REWRITE_TAC[real_abs; REAL_LE_RNEG; REAL_NEG_NEG; REAL_ADD_LID] THEN
  MESON_TAC[REAL_LE_TOTAL; REAL_LE_ANTISYM; REAL_NEG_0]);;

(* ------------------------------------------------------------------------- *)
(* First, the conversions on integer constants.                              *)
(* ------------------------------------------------------------------------- *)

let REAL_INT_LE_CONV,REAL_INT_LT_CONV,
    REAL_INT_GE_CONV,REAL_INT_GT_CONV,REAL_INT_EQ_CONV =
  let tth =
    TAUT `(F /\ F <=> F) /\ (F /\ T <=> F) /\
          (T /\ F <=> F) /\ (T /\ T <=> T)` in
  let nth = TAUT `(~T <=> F) /\ (~F <=> T)` in
  let NUM2_EQ_CONV = BINOP_CONV NUM_EQ_CONV THENC GEN_REWRITE_CONV I [tth] in
  let NUM2_NE_CONV =
    RAND_CONV NUM2_EQ_CONV THENC
    GEN_REWRITE_CONV I [nth] in
  let [pth_le1; pth_le2a; pth_le2b; pth_le3] = (CONJUNCTS o prove)
   (`(--(&m) <= &n <=> T) /\
     (&m <= &n <=> m <= n) /\
     (--(&m) <= --(&n) <=> n <= m) /\
     (&m <= --(&n) <=> (m = 0) /\ (n = 0))`,
    REWRITE_TAC[REAL_LE_NEG2] THEN
    REWRITE_TAC[REAL_LE_LNEG; REAL_LE_RNEG] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; LE_0] THEN
    REWRITE_TAC[LE; ADD_EQ_0]) in
  let REAL_INT_LE_CONV = FIRST_CONV
   [GEN_REWRITE_CONV I [pth_le1];
    GEN_REWRITE_CONV I [pth_le2a; pth_le2b] THENC NUM_LE_CONV;
    GEN_REWRITE_CONV I [pth_le3] THENC NUM2_EQ_CONV] in
  let [pth_lt1; pth_lt2a; pth_lt2b; pth_lt3] = (CONJUNCTS o prove)
   (`(&m < --(&n) <=> F) /\
     (&m < &n <=> m < n) /\
     (--(&m) < --(&n) <=> n < m) /\
     (--(&m) < &n <=> ~((m = 0) /\ (n = 0)))`,
    REWRITE_TAC[pth_le1; pth_le2a; pth_le2b; pth_le3;
                GSYM NOT_LE; real_lt] THEN
    CONV_TAC TAUT) in
  let REAL_INT_LT_CONV = FIRST_CONV
   [GEN_REWRITE_CONV I [pth_lt1];
    GEN_REWRITE_CONV I [pth_lt2a; pth_lt2b] THENC NUM_LT_CONV;
    GEN_REWRITE_CONV I [pth_lt3] THENC NUM2_NE_CONV] in
  let [pth_ge1; pth_ge2a; pth_ge2b; pth_ge3] = (CONJUNCTS o prove)
   (`(&m >= --(&n) <=> T) /\
     (&m >= &n <=> n <= m) /\
     (--(&m) >= --(&n) <=> m <= n) /\
     (--(&m) >= &n <=> (m = 0) /\ (n = 0))`,
    REWRITE_TAC[pth_le1; pth_le2a; pth_le2b; pth_le3; real_ge] THEN
    CONV_TAC TAUT) in
  let REAL_INT_GE_CONV = FIRST_CONV
   [GEN_REWRITE_CONV I [pth_ge1];
    GEN_REWRITE_CONV I [pth_ge2a; pth_ge2b] THENC NUM_LE_CONV;
    GEN_REWRITE_CONV I [pth_ge3] THENC NUM2_EQ_CONV] in
  let [pth_gt1; pth_gt2a; pth_gt2b; pth_gt3] = (CONJUNCTS o prove)
   (`(--(&m) > &n <=> F) /\
     (&m > &n <=> n < m) /\
     (--(&m) > --(&n) <=> m < n) /\
     (&m > --(&n) <=> ~((m = 0) /\ (n = 0)))`,
    REWRITE_TAC[pth_lt1; pth_lt2a; pth_lt2b; pth_lt3; real_gt] THEN
    CONV_TAC TAUT) in
  let REAL_INT_GT_CONV = FIRST_CONV
   [GEN_REWRITE_CONV I [pth_gt1];
    GEN_REWRITE_CONV I [pth_gt2a; pth_gt2b] THENC NUM_LT_CONV;
    GEN_REWRITE_CONV I [pth_gt3] THENC NUM2_NE_CONV] in
  let [pth_eq1a; pth_eq1b; pth_eq2a; pth_eq2b] = (CONJUNCTS o prove)
   (`((&m = &n) <=> (m = n)) /\
     ((--(&m) = --(&n)) <=> (m = n)) /\
     ((--(&m) = &n) <=> (m = 0) /\ (n = 0)) /\
     ((&m = --(&n)) <=> (m = 0) /\ (n = 0))`,
    REWRITE_TAC[GSYM REAL_LE_ANTISYM; GSYM LE_ANTISYM] THEN
    REWRITE_TAC[pth_le1; pth_le2a; pth_le2b; pth_le3; LE; LE_0] THEN
    CONV_TAC TAUT) in
  let REAL_INT_EQ_CONV = FIRST_CONV
   [GEN_REWRITE_CONV I [pth_eq1a; pth_eq1b] THENC NUM_EQ_CONV;
    GEN_REWRITE_CONV I [pth_eq2a; pth_eq2b] THENC NUM2_EQ_CONV] in
  REAL_INT_LE_CONV,REAL_INT_LT_CONV,
  REAL_INT_GE_CONV,REAL_INT_GT_CONV,REAL_INT_EQ_CONV;;

let REAL_INT_NEG_CONV =
  let pth = prove
   (`(--(&0) = &0) /\
     (--(--(&x)) = &x)`,
    REWRITE_TAC[REAL_NEG_NEG; REAL_NEG_0]) in
  GEN_REWRITE_CONV I [pth];;

let REAL_INT_MUL_CONV =
  let pth0 = prove
   (`(&0 * &x = &0) /\
     (&0 * --(&x) = &0) /\
     (&x * &0 = &0) /\
     (--(&x) * &0 = &0)`,
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO])
  and pth1,pth2 = (CONJ_PAIR o prove)
   (`((&m * &n = &(m * n)) /\
      (--(&m) * --(&n) = &(m * n))) /\
     ((--(&m) * &n = --(&(m * n))) /\
      (&m * --(&n) = --(&(m * n))))`,
    REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL]) in
  FIRST_CONV
   [GEN_REWRITE_CONV I [pth0];
    GEN_REWRITE_CONV I [pth1] THENC RAND_CONV NUM_MULT_CONV;
    GEN_REWRITE_CONV I [pth2] THENC RAND_CONV(RAND_CONV NUM_MULT_CONV)];;

let REAL_INT_ADD_CONV =
  let neg_tm = `(--)` in
  let amp_tm = `&` in
  let add_tm = `(+)` in
  let dest = dest_binop `(+)` in
  let m_tm = `m:num` and n_tm = `n:num` in
  let pth0 = prove
   (`(--(&m) + &m = &0) /\
     (&m + --(&m) = &0)`,
    REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_RINV]) in
  let [pth1; pth2; pth3; pth4; pth5; pth6] = (CONJUNCTS o prove)
   (`(--(&m) + --(&n) = --(&(m + n))) /\
     (--(&m) + &(m + n) = &n) /\
     (--(&(m + n)) + &m = --(&n)) /\
     (&(m + n) + --(&m) = &n) /\
     (&m + --(&(m + n)) = --(&n)) /\
     (&m + &n = &(m + n))`,
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_NEG_ADD] THEN
    REWRITE_TAC[REAL_ADD_ASSOC; REAL_ADD_LINV; REAL_ADD_LID] THEN
    REWRITE_TAC[REAL_ADD_RINV; REAL_ADD_LID] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    REWRITE_TAC[REAL_ADD_ASSOC; REAL_ADD_LINV; REAL_ADD_LID] THEN
    REWRITE_TAC[REAL_ADD_RINV; REAL_ADD_LID]) in
  GEN_REWRITE_CONV I [pth0] ORELSEC
  (fun tm ->
    try let l,r = dest tm in
        if not(is_realintconst l) || not(is_realintconst r) then failwith ""
        else if rator l = neg_tm then
          if rator r = neg_tm then
            let th1 = INST [rand(rand l),m_tm; rand(rand r),n_tm] pth1 in
            let tm1 = rand(rand(rand(concl th1))) in
            let th2 = AP_TERM neg_tm (AP_TERM amp_tm (NUM_ADD_CONV tm1)) in
            TRANS th1 th2
          else
            let m = rand(rand l) and n = rand r in
            let m' = dest_numeral m and n' = dest_numeral n in
            if m' <=/ n' then
              let p = mk_numeral (n' -/ m') in
              let th1 = INST [m,m_tm; p,n_tm] pth2 in
              let th2 = NUM_ADD_CONV (rand(rand(lhand(concl th1)))) in
              let th3 = AP_TERM (rator tm) (AP_TERM amp_tm (SYM th2)) in
              TRANS th3 th1
            else
              let p = mk_numeral (m' -/ n') in
              let th1 = INST [n,m_tm; p,n_tm] pth3 in
              let th2 = NUM_ADD_CONV (rand(rand(lhand(lhand(concl th1))))) in
              let th3 = AP_TERM neg_tm (AP_TERM amp_tm (SYM th2)) in
              let th4 = AP_THM (AP_TERM add_tm th3) (rand tm) in
              TRANS th4 th1
        else
          if rator r = neg_tm then
            let m = rand l and n = rand(rand r) in
            let m' = dest_numeral m and n' = dest_numeral n in
            if n' <=/ m' then
              let p = mk_numeral (m' -/ n') in
              let th1 = INST [n,m_tm; p,n_tm] pth4 in
              let th2 = NUM_ADD_CONV (rand(lhand(lhand(concl th1)))) in
              let th3 = AP_TERM add_tm (AP_TERM amp_tm (SYM th2)) in
              let th4 = AP_THM th3 (rand tm) in
              TRANS th4 th1
            else
             let p = mk_numeral (n' -/ m') in
             let th1 = INST [m,m_tm; p,n_tm] pth5 in
             let th2 = NUM_ADD_CONV (rand(rand(rand(lhand(concl th1))))) in
             let th3 = AP_TERM neg_tm (AP_TERM amp_tm (SYM th2)) in
             let th4 = AP_TERM (rator tm) th3 in
             TRANS th4 th1
          else
            let th1 = INST [rand l,m_tm; rand r,n_tm] pth6 in
            let tm1 = rand(rand(concl th1)) in
            let th2 = AP_TERM amp_tm (NUM_ADD_CONV tm1) in
            TRANS th1 th2
    with Failure _ -> failwith "REAL_INT_ADD_CONV");;

let REAL_INT_SUB_CONV =
  GEN_REWRITE_CONV I [real_sub] THENC
  TRY_CONV(RAND_CONV REAL_INT_NEG_CONV) THENC
  REAL_INT_ADD_CONV;;

let REAL_INT_POW_CONV =
  let pth1,pth2 = (CONJ_PAIR o prove)
   (`(&x pow n = &(x EXP n)) /\
     ((--(&x)) pow n = if EVEN n then &(x EXP n) else --(&(x EXP n)))`,
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_POW_NEG]) in
  let tth = prove
   (`((if T then x:real else y) = x) /\ ((if F then x:real else y) = y)`,
    REWRITE_TAC[]) in
  let neg_tm = `(--)` in
  (GEN_REWRITE_CONV I [pth1] THENC RAND_CONV NUM_EXP_CONV) ORELSEC
  (GEN_REWRITE_CONV I [pth2] THENC
   RATOR_CONV(RATOR_CONV(RAND_CONV NUM_EVEN_CONV)) THENC
   GEN_REWRITE_CONV I [tth] THENC
   (fun tm -> if rator tm = neg_tm then RAND_CONV(RAND_CONV NUM_EXP_CONV) tm
              else RAND_CONV NUM_EXP_CONV  tm));;

let REAL_INT_ABS_CONV =
  let pth = prove
   (`(abs(--(&x)) = &x) /\
     (abs(&x) = &x)`,
    REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM]) in
  GEN_REWRITE_CONV I [pth];;

let real_int_red_conv_list =
  [`x <= y`,REAL_INT_LE_CONV;
   `x < y`,REAL_INT_LT_CONV;
   `x >= y`,REAL_INT_GE_CONV;
   `x > y`,REAL_INT_GT_CONV;
   `x:real = y`,REAL_INT_EQ_CONV;
   `--x`,CHANGED_CONV REAL_INT_NEG_CONV;
   `abs(x)`,REAL_INT_ABS_CONV;
   `x + y`,REAL_INT_ADD_CONV;
   `x - y`,REAL_INT_SUB_CONV;
   `x * y`,REAL_INT_MUL_CONV;
   `x pow n`,REAL_INT_POW_CONV];;

let REAL_INT_RED_CONV =
  let gconv_net = itlist (uncurry net_of_conv) real_int_red_conv_list
    (basic_net()) in
  REWRITES_CONV gconv_net;;

let REAL_INT_REDUCE_CONV = DEPTH_CONV REAL_INT_RED_CONV;;

let real_int_compute_add_convs =
  let convlist = map (fun pat,the_conv ->
    let c,args = strip_comb pat in (c,length args,the_conv))
    real_int_red_conv_list in
  fun (compset:Compute.compset) ->
    itlist (fun newc () -> Compute.add_conv newc compset) convlist ();;

let REAL_INT_COMPUTE_CONV =
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  real_int_compute_add_convs cs;
  Compute.WEAK_CBV_CONV cs;;
