(* ========================================================================= *)
(* Calculation with naturals.                                                *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                (c) Copyright, Mario Carneiro 2020                         *)
(* ========================================================================= *)

needs "wf.ml";;

(* ------------------------------------------------------------------------- *)
(* Simple rule to get rid of NUMERAL constant.                               *)
(* ------------------------------------------------------------------------- *)

let DENUMERAL = GEN_REWRITE_RULE DEPTH_CONV [NUMERAL];;

(* ------------------------------------------------------------------------- *)
(* Big collection of rewrites to do trivial arithmetic.                      *)
(*                                                                           *)
(* Note that we have none for DIV and MOD, and that PRE and SUB are a bit    *)
(* inefficient; log(n)^2 instead of log(n).                                  *)
(* ------------------------------------------------------------------------- *)

let ARITH_ZERO = prove
 (`(NUMERAL 0 = 0) /\
   (BIT0 _0 = _0)`,
  REWRITE_TAC[NUMERAL; BIT0; DENUMERAL ADD_CLAUSES]);;

let BIT0_0 = prove
  (`BIT0 0 = 0`,
   REWRITE_TAC [NUMERAL; ARITH_ZERO]);;

let BIT1_0 = prove
 (`BIT1 0 = 1`,
  REWRITE_TAC [NUMERAL]);;

let ARITH_SUC = prove
 (`(!n. SUC(NUMERAL n) = NUMERAL(SUC n)) /\
   (SUC _0 = BIT1 _0) /\
   (!n. SUC (BIT0 n) = BIT1 n) /\
   (!n. SUC (BIT1 n) = BIT0 (SUC n))`,
  REWRITE_TAC[NUMERAL; BIT0; BIT1; DENUMERAL ADD_CLAUSES]);;

let ARITH_PRE = prove
 (`(!n. PRE(NUMERAL n) = NUMERAL(PRE n)) /\
   (PRE _0 = _0) /\
   (!n. PRE(BIT0 n) = if n = _0 then _0 else BIT1 (PRE n)) /\
   (!n. PRE(BIT1 n) = BIT0 n)`,
  REWRITE_TAC[NUMERAL; BIT1; BIT0; DENUMERAL PRE] THEN INDUCT_TAC THEN
  REWRITE_TAC[NUMERAL; DENUMERAL PRE; DENUMERAL ADD_CLAUSES; DENUMERAL NOT_SUC;
              ARITH_ZERO]);;

let ARITH_ADD = prove
 (`(!m n. NUMERAL(m) + NUMERAL(n) = NUMERAL(m + n)) /\
   (_0 + _0 = _0) /\
   (!n. _0 + BIT0 n = BIT0 n) /\
   (!n.        _0 + BIT1 n = BIT1 n) /\
   (!n.   BIT0 n + _0 = BIT0 n) /\
   (!n.   BIT1 n + _0 = BIT1 n) /\
   (!m n. BIT0 m + BIT0 n = BIT0 (m + n)) /\
   (!m n. BIT0 m + BIT1 n = BIT1 (m + n)) /\
   (!m n. BIT1 m + BIT0 n = BIT1 (m + n)) /\
   (!m n. BIT1 m + BIT1 n = BIT0 (SUC(m + n)))`,
  PURE_REWRITE_TAC[NUMERAL; BIT0; BIT1; DENUMERAL ADD_CLAUSES; SUC_INJ] THEN
  REWRITE_TAC[ADD_AC]);;

let ARITH_MULT = prove
 (`(!m n. NUMERAL(m) * NUMERAL(n) = NUMERAL(m * n)) /\
   (_0 * _0 = _0) /\
   (!n. _0 * BIT0 n = _0) /\
   (!n. _0 * BIT1 n = _0) /\
   (!n. BIT0 n * _0 = _0) /\
   (!n. BIT1 n * _0 = _0) /\
   (!m n. BIT0 m * BIT0 n = BIT0 (BIT0 (m * n))) /\
   (!m n. BIT0 m * BIT1 n = BIT0 m + BIT0 (BIT0 (m * n))) /\
   (!m n. BIT1 m * BIT0 n = BIT0 n + BIT0 (BIT0 (m * n))) /\
   (!m n. BIT1 m * BIT1 n = BIT1 m + BIT0 n + BIT0 (BIT0 (m * n)))`,
  PURE_REWRITE_TAC[NUMERAL; BIT0; BIT1; DENUMERAL MULT_CLAUSES;
                   DENUMERAL ADD_CLAUSES; SUC_INJ] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; ADD_AC]);;

let ARITH_EXP = prove
 (`(!m n. (NUMERAL m) EXP (NUMERAL n) = NUMERAL(m EXP n)) /\
   (_0 EXP _0 = BIT1 _0) /\
   (!m. (BIT0 m) EXP _0 = BIT1 _0) /\
   (!m. (BIT1 m) EXP _0 = BIT1 _0) /\
   (!n. _0 EXP (BIT0 n) = (_0 EXP n) * (_0 EXP n)) /\
   (!m n. (BIT0 m) EXP (BIT0 n) = ((BIT0 m) EXP n) * ((BIT0 m) EXP n)) /\
   (!m n. (BIT1 m) EXP (BIT0 n) = ((BIT1 m) EXP n) * ((BIT1 m) EXP n)) /\
   (!n. _0 EXP (BIT1 n) = _0) /\
   (!m n. (BIT0 m) EXP (BIT1 n) =
        BIT0 m * ((BIT0 m) EXP n) * ((BIT0 m) EXP n)) /\
   (!m n. (BIT1 m) EXP (BIT1 n) =
        BIT1 m * ((BIT1 m) EXP n) * ((BIT1 m) EXP n))`,
  REWRITE_TAC[NUMERAL] THEN REPEAT STRIP_TAC THEN
  TRY(GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [BIT0; BIT1]) THEN
  REWRITE_TAC[DENUMERAL EXP; DENUMERAL MULT_CLAUSES; EXP_ADD]);;

let ARITH_EVEN = prove
 (`(!n. EVEN(NUMERAL n) <=> EVEN n) /\
   (EVEN _0 <=> T) /\
   (!n. EVEN(BIT0 n) <=> T) /\
   (!n. EVEN(BIT1 n) <=> F)`,
  REWRITE_TAC[NUMERAL; BIT1; BIT0; DENUMERAL EVEN; EVEN_ADD]);;

let ARITH_ODD = prove
 (`(!n. ODD(NUMERAL n) <=> ODD n) /\
   (ODD _0 <=> F) /\
   (!n. ODD(BIT0 n) <=> F) /\
   (!n. ODD(BIT1 n) <=> T)`,
  REWRITE_TAC[NUMERAL; BIT1; BIT0; DENUMERAL ODD; ODD_ADD]);;

let ARITH_LE = prove
 (`(!m n. NUMERAL m <= NUMERAL n <=> m <= n) /\
   ((_0 <= _0) <=> T) /\
   (!n. (BIT0 n <= _0) <=> n <= _0) /\
   (!n. (BIT1 n <= _0) <=> F) /\
   (!n. (_0 <= BIT0 n) <=> T) /\
   (!n. (_0 <= BIT1 n) <=> T) /\
   (!m n. (BIT0 m <= BIT0 n) <=> m <= n) /\
   (!m n. (BIT0 m <= BIT1 n) <=> m <= n) /\
   (!m n. (BIT1 m <= BIT0 n) <=> m < n) /\
   (!m n. (BIT1 m <= BIT1 n) <=> m <= n)`,
  REWRITE_TAC[NUMERAL; BIT1; BIT0; DENUMERAL NOT_SUC;
      DENUMERAL(GSYM NOT_SUC); SUC_INJ] THEN
  REWRITE_TAC[DENUMERAL LE_0] THEN REWRITE_TAC[DENUMERAL LE; GSYM MULT_2] THEN
  REWRITE_TAC[LE_MULT_LCANCEL; SUC_INJ;
              DENUMERAL MULT_EQ_0; DENUMERAL NOT_SUC] THEN
  REWRITE_TAC[DENUMERAL NOT_SUC] THEN REWRITE_TAC[LE_SUC_LT] THEN
  REWRITE_TAC[LT_MULT_LCANCEL] THEN
  SUBGOAL_THEN `2 = SUC 1` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[NUMERAL; BIT0; BIT1; DENUMERAL ADD_CLAUSES];
    REWRITE_TAC[DENUMERAL NOT_SUC; NOT_SUC; EQ_MULT_LCANCEL] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[DISJ_SYM] LE_LT] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
    SUBGOAL_THEN `~(SUC 1 * m = SUC (SUC 1 * n))`
      (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
    REWRITE_TAC[EVEN_MULT; EVEN_ADD; NUMERAL; BIT1; EVEN]]);;

let ARITH_LT = prove
 (`(!m n. NUMERAL m < NUMERAL n <=> m < n) /\
   ((_0 < _0) <=> F) /\
   (!n. (BIT0 n < _0) <=> F) /\
   (!n. (BIT1 n < _0) <=> F) /\
   (!n. (_0 < BIT0 n) <=> _0 < n) /\
   (!n. (_0 < BIT1 n) <=> T) /\
   (!m n. (BIT0 m < BIT0 n) <=> m < n) /\
   (!m n. (BIT0 m < BIT1 n) <=> m <= n) /\
   (!m n. (BIT1 m < BIT0 n) <=> m < n) /\
   (!m n. (BIT1 m < BIT1 n) <=> m < n)`,
  REWRITE_TAC[NUMERAL; GSYM NOT_LE; ARITH_LE] THEN
  REWRITE_TAC[DENUMERAL LE]);;

let ARITH_GE = REWRITE_RULE[GSYM GE; GSYM GT] ARITH_LE;;

let ARITH_GT = REWRITE_RULE[GSYM GE; GSYM GT] ARITH_LT;;

let ARITH_EQ = prove
 (`(!m n. (NUMERAL m = NUMERAL n) <=> (m = n)) /\
   ((_0 = _0) <=> T) /\
   (!n. (BIT0 n = _0) <=> (n = _0)) /\
   (!n. (BIT1 n = _0) <=> F) /\
   (!n. (_0 = BIT0 n) <=> (_0 = n)) /\
   (!n. (_0 = BIT1 n) <=> F) /\
   (!m n. (BIT0 m = BIT0 n) <=> (m = n)) /\
   (!m n. (BIT0 m = BIT1 n) <=> F) /\
   (!m n. (BIT1 m = BIT0 n) <=> F) /\
   (!m n. (BIT1 m = BIT1 n) <=> (m = n))`,
  REWRITE_TAC[NUMERAL; GSYM LE_ANTISYM; ARITH_LE] THEN
  REWRITE_TAC[LET_ANTISYM; LTE_ANTISYM; DENUMERAL LE_0]);;

let ARITH_SUB = prove
 (`(!m n. NUMERAL m - NUMERAL n = NUMERAL(m - n)) /\
   (_0 - _0 = _0) /\
   (!n. _0 - BIT0 n = _0) /\
   (!n. _0 - BIT1 n = _0) /\
   (!n. BIT0 n - _0 = BIT0 n) /\
   (!n. BIT1 n - _0 = BIT1 n) /\
   (!m n. BIT0 m - BIT0 n = BIT0 (m - n)) /\
   (!m n. BIT0 m - BIT1 n = PRE(BIT0 (m - n))) /\
   (!m n. BIT1 m - BIT0 n = if n <= m then BIT1 (m - n) else _0) /\
   (!m n. BIT1 m - BIT1 n = BIT0 (m - n))`,
  REWRITE_TAC[NUMERAL; DENUMERAL SUB_0] THEN PURE_REWRITE_TAC[BIT0; BIT1] THEN
  REWRITE_TAC[GSYM MULT_2; SUB_SUC; LEFT_SUB_DISTRIB] THEN
  REWRITE_TAC[SUB] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[DENUMERAL SUB_EQ_0] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
  ASM_REWRITE_TAC[LE_SUC_LT; LT_MULT_LCANCEL; ARITH_EQ] THEN
  POP_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[ADD1; LEFT_ADD_DISTRIB] THEN
  REWRITE_TAC[ADD_SUB2; GSYM ADD_ASSOC]);;

let ARITH = end_itlist CONJ
  [ARITH_ZERO; ARITH_SUC; ARITH_PRE;
   ARITH_ADD; ARITH_MULT; ARITH_EXP;
   ARITH_EVEN; ARITH_ODD;
   ARITH_EQ; ARITH_LE; ARITH_LT; ARITH_GE; ARITH_GT;
   ARITH_SUB];;

let EXP_2_NE_0 = prove
 (`!n. ~(2 EXP n = 0)`,
  REWRITE_TAC [EXP_EQ_0; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Now more delicate conversions for situations where efficiency matters.    *)
(* ------------------------------------------------------------------------- *)

let NUM_EVEN_CONV =
  let tth,rths = CONJ_PAIR ARITH_EVEN in
  GEN_REWRITE_CONV I [tth] THENC GEN_REWRITE_CONV I [rths];;

let NUM_ODD_CONV =
  let tth,rths = CONJ_PAIR ARITH_ODD in
  GEN_REWRITE_CONV I [tth] THENC GEN_REWRITE_CONV I [rths];;

let NUM_SUC_CONV,NUM_ADD_CONV,NUM_MULT_CONV,NUM_EXP_CONV,
    NUM_LT_CONV,NUM_LE_CONV,NUM_EQ_CONV =
  let num_ty = type_of(lhand(concl ZERO_DEF)) in
  let Comb(NUMERAL_tm,Comb(BIT0_tm,Comb(BIT1_tm,zero_tm))) =
    mk_small_numeral 2
  and suc_tm = rator(rand(concl TWO))
  and one_tm = rand(mk_small_numeral 1)
  and add_tm = rator(rator(lhand(snd(strip_forall(concl ADD_0)))))
  and mul_tm = rator(rator(rand(snd(strip_forall(concl EXP_2)))))
  and exp_tm = rator(rator(lhand(snd(strip_forall(concl EXP_2)))))
  and eq_tm = rator(rator(concl TWO)) in
  let num_0 = num 0 and num_1 = num 1 and num_2 = num 2 in
  let a_tm = mk_var("a",num_ty)
  and b_tm = mk_var("b",num_ty)
  and c_tm = mk_var("c",num_ty)
  and d_tm = mk_var("d",num_ty)
  and e_tm = mk_var("e",num_ty)
  and h_tm = mk_var("h",num_ty)
  and l_tm = mk_var("l",num_ty)
  and m_tm = mk_var("m",num_ty)
  and n_tm = mk_var("n",num_ty)
  and p_tm = mk_var("p",num_ty) in
  let STANDARDIZE =
    let ilist = [BIT0_tm,BIT0_tm; BIT1_tm,BIT1_tm; zero_tm,zero_tm;
                 suc_tm,suc_tm; add_tm,add_tm; mul_tm,mul_tm;
                 exp_tm,exp_tm; eq_tm,eq_tm; NUMERAL_tm,NUMERAL_tm;
                 a_tm,a_tm; b_tm,b_tm; c_tm,c_tm; d_tm,d_tm; e_tm,e_tm;
                 h_tm,h_tm; l_tm,l_tm; m_tm,m_tm; n_tm,n_tm; p_tm,p_tm] in
    let rec replace tm =
      match tm with
        Var(_,_) | Const(_,_) -> rev_assocd tm ilist tm
      | Comb(s,t) -> mk_comb(replace s,replace t)
      | Abs(_,_) -> failwith "replace" in
    fun th -> let tm' = replace (concl th) in EQ_MP (REFL tm') th in
  let REFL_bit0 = STANDARDIZE(REFL BIT0_tm)
  and REFL_bit1 = STANDARDIZE(REFL BIT1_tm) in
  let AP_BIT0 th = MK_COMB(REFL_bit0,th)
  and AP_BIT1 th = MK_COMB(REFL_bit1,th)
  and QUICK_PROVE_HYP ath bth = EQ_MP (DEDUCT_ANTISYM_RULE ath bth) ath in
  let rec dest_raw_numeral tm =
    match tm with
      Comb(Const("BIT1",_),t) -> num_2 */ dest_raw_numeral t +/ num_1
    | Comb(Const("BIT0",_),t) -> num_2 */ dest_raw_numeral t
    | Const("_0",_) -> num_0 in
  let bitcounts =
    let rec bctr w z tm =
      match tm with
        Const("_0",_) -> (w,z)
      | Comb(Const("BIT0",_),t) -> bctr w (z + 1) t
      | Comb(Const("BIT1",_),t) -> bctr (w + 1) z t
      | _ -> failwith "malformed numeral" in
    bctr 0 0 in
  let rec wellformed tm =
    match tm with
      Const("_0",_) -> true
    | Comb(Const("BIT0",_),t)|Comb(Const("BIT1",_),t) -> wellformed t
    | _ -> false in
  let rec orderrelation mtm ntm =
    if mtm == ntm then
      if wellformed mtm then 0 else failwith "orderrelation"
    else
      match (mtm,ntm) with
        Const("_0",_),Const("_0",_) -> 0
      | Const("_0",_),_ ->
           if wellformed ntm then -1 else failwith "orderrelation"
      | _, Const("_0",_) ->
           if wellformed ntm then 1 else failwith "orderrelation"
      | Comb(Const("BIT0",_),mt),Comb(Const("BIT0",_),nt)
      | Comb(Const("BIT1",_),mt),Comb(Const("BIT1",_),nt) ->
          orderrelation mt nt
      | Comb(Const("BIT0",_),mt),Comb(Const("BIT1",_),nt) ->
          if orderrelation mt nt > 0 then 1 else -1
      | Comb(Const("BIT1",_),mt),Comb(Const("BIT0",_),nt) ->
          if orderrelation mt nt < 0 then -1 else 1 in
  let doublebn tm = if tm = zero_tm then tm else mk_comb(BIT0_tm,tm) in
  let rec subbn mtm ntm =
    match (mtm,ntm) with
      (_,Const("_0",_)) -> mtm
    | (Comb(Const("BIT0",_),mt),Comb(Const("BIT0",_),nt)) ->
          doublebn (subbn mt nt)
    | (Comb(Const("BIT1",_),mt),Comb(Const("BIT1",_),nt)) ->
          doublebn (subbn mt nt)
    | (Comb(Const("BIT1",_),mt),Comb(Const("BIT0",_),nt)) ->
          mk_comb(BIT1_tm,subbn mt nt)
    | (Comb(Const("BIT0",_),mt),Comb(Const("BIT1",_),nt)) ->
          mk_comb(BIT1_tm,sbcbn mt nt)
    | _ -> failwith "malformed numeral or wrong relation"
  and sbcbn mtm ntm =
    match (mtm,ntm) with
    | (Comb(Const("BIT0",_),mt),Const("_0",_)) ->
          mk_comb(BIT1_tm,sbcbn mt ntm)
    | (Comb(Const("BIT1",_),mt),Const("_0",_)) ->
          doublebn mt
    | (Comb(Const("BIT0",_),mt),Comb(Const("BIT0",_),nt)) ->
          mk_comb(BIT1_tm,sbcbn mt nt)
    | (Comb(Const("BIT1",_),mt),Comb(Const("BIT1",_),nt)) ->
          mk_comb(BIT1_tm,sbcbn mt nt)
    | (Comb(Const("BIT1",_),mt),Comb(Const("BIT0",_),nt)) ->
          doublebn (subbn mt nt)
    | (Comb(Const("BIT0",_),mt),Comb(Const("BIT1",_),nt)) ->
          doublebn (sbcbn mt nt)
    | _ -> failwith "malformed numeral or wrong relation" in
  let topsplit tm =
    match tm with
     Const("_0",_) -> 0,zero_tm
   | Comb(Const("BIT1",_),Const("_0",_)) -> 1,zero_tm
   | Comb(Const("BIT0",_),Comb(Const("BIT1",_),Const("_0",_))) -> 2,zero_tm
   | Comb(Const("BIT1",_),Comb(Const("BIT1",_),Const("_0",_))) -> 3,zero_tm
   | Comb(Const("BIT0",_),Comb(Const("BIT0",_),Comb(Const("BIT1",_),Const("_0",_)))) -> 4,zero_tm
   | Comb(Const("BIT1",_),Comb(Const("BIT0",_),Comb(Const("BIT1",_),Const("_0",_)))) -> 5,zero_tm
   | Comb(Const("BIT0",_),Comb(Const("BIT1",_),Comb(Const("BIT1",_),Const("_0",_)))) -> 6,zero_tm
   | Comb(Const("BIT1",_),Comb(Const("BIT1",_),Comb(Const("BIT1",_),Const("_0",_)))) -> 7,zero_tm
   | Comb(Const("BIT0",_),Comb(Const("BIT0",_),Comb(Const("BIT0",_),Comb(Const("BIT0",_),n)))) -> 0,n
   | Comb(Const("BIT1",_),Comb(Const("BIT0",_),Comb(Const("BIT0",_),Comb(Const("BIT0",_),n)))) -> 1,n
   | Comb(Const("BIT0",_),Comb(Const("BIT1",_),Comb(Const("BIT0",_),Comb(Const("BIT0",_),n)))) -> 2,n
   | Comb(Const("BIT1",_),Comb(Const("BIT1",_),Comb(Const("BIT0",_),Comb(Const("BIT0",_),n)))) -> 3,n
   | Comb(Const("BIT0",_),Comb(Const("BIT0",_),Comb(Const("BIT1",_),Comb(Const("BIT0",_),n)))) -> 4,n
   | Comb(Const("BIT1",_),Comb(Const("BIT0",_),Comb(Const("BIT1",_),Comb(Const("BIT0",_),n)))) -> 5,n
   | Comb(Const("BIT0",_),Comb(Const("BIT1",_),Comb(Const("BIT1",_),Comb(Const("BIT0",_),n)))) -> 6,n
   | Comb(Const("BIT1",_),Comb(Const("BIT1",_),Comb(Const("BIT1",_),Comb(Const("BIT0",_),n)))) -> 7,n
   | Comb(Const("BIT0",_),Comb(Const("BIT0",_),Comb(Const("BIT0",_),Comb(Const("BIT1",_),n)))) -> 8,n
   | Comb(Const("BIT1",_),Comb(Const("BIT0",_),Comb(Const("BIT0",_),Comb(Const("BIT1",_),n)))) -> 9,n
   | Comb(Const("BIT0",_),Comb(Const("BIT1",_),Comb(Const("BIT0",_),Comb(Const("BIT1",_),n)))) -> 10,n
   | Comb(Const("BIT1",_),Comb(Const("BIT1",_),Comb(Const("BIT0",_),Comb(Const("BIT1",_),n)))) -> 11,n
   | Comb(Const("BIT0",_),Comb(Const("BIT0",_),Comb(Const("BIT1",_),Comb(Const("BIT1",_),n)))) -> 12,n
   | Comb(Const("BIT1",_),Comb(Const("BIT0",_),Comb(Const("BIT1",_),Comb(Const("BIT1",_),n)))) -> 13,n
   | Comb(Const("BIT0",_),Comb(Const("BIT1",_),Comb(Const("BIT1",_),Comb(Const("BIT1",_),n)))) -> 14,n
   | Comb(Const("BIT1",_),Comb(Const("BIT1",_),Comb(Const("BIT1",_),Comb(Const("BIT1",_),n)))) -> 15,n
   | _ -> failwith "malformed numeral" in
  let NUM_ADD_RULE,NUM_ADC_RULE =
    let rec mk_compnumeral k base =
      if k = 0 then base else
      let t = mk_compnumeral (k / 2) base in
      if k mod 2 = 1 then mk_comb(BIT1_tm,t) else mk_comb(BIT0_tm,t) in
    let bases v =
        let part2 = map (fun k -> mk_compnumeral k v) (8--15) in
        let part1 = map (subst[mk_comb(BIT0_tm,v),mk_comb(BIT1_tm,v)])
                        part2
        and part0 = map (fun k -> mk_compnumeral k zero_tm) (0--15) in
        part0 @ part1 @ part2 in
    let starts =
      allpairs (fun mtm ntm ->
        mk_comb(mk_comb(add_tm,mtm),ntm)) (bases m_tm) (bases n_tm) in
    let BITS_INJ = (STANDARDIZE o prove)
     (`(BIT0 m = BIT0 n <=> m = n) /\
       (BIT1 m = BIT1 n <=> m = n)`,
      REWRITE_TAC[BIT0; BIT1] THEN
      REWRITE_TAC[GSYM MULT_2] THEN
      REWRITE_TAC[SUC_INJ; EQ_MULT_LCANCEL; ARITH_EQ]) in
    let ARITH_0 = (STANDARDIZE o MESON[NUMERAL; ADD_CLAUSES])
      `m + _0 = m /\ _0 + n = n` in
    let patadj = subst[`SUC(m + _0)`,`SUC m`; `SUC(_0 + n)`,`SUC n`] in
    let mkclauses sucflag t =
      let tm = if sucflag then mk_comb(suc_tm,t) else t in
      let th1 = PURE_REWRITE_CONV[ARITH_ADD; ARITH_SUC; ARITH_0] tm in
      let tm1 = patadj(rand(concl th1)) in
      if not(free_in add_tm tm1) then th1,
         (if free_in m_tm tm1 then 0 else 1) else
      let ptm = rand(rand(rand(rand tm1))) in
      let tmc = mk_eq(mk_eq(ptm,p_tm),mk_eq(tm,subst[p_tm,ptm] tm1)) in
      EQT_ELIM(REWRITE_CONV[ARITH_ADD; ARITH_SUC; ARITH_0; BITS_INJ] tmc),
      (if free_in suc_tm tm1 then 3 else 2) in
    let add_clauses,add_flags =
      let l1,l2 = unzip(map (mkclauses false) starts) in
      Array.of_list(map STANDARDIZE l1),Array.of_list l2 in
    let adc_clauses,adc_flags =
      let l1,l2 = unzip(map (mkclauses true) starts) in
      Array.of_list(map STANDARDIZE l1),Array.of_list l2 in
    let rec NUM_ADD_RULE mtm ntm =
      let m_lo,m_hi = topsplit mtm
      and n_lo,n_hi = topsplit ntm in
      let m_ind = if m_hi = zero_tm then m_lo else m_lo + 16
      and n_ind = if n_hi = zero_tm then n_lo else n_lo + 16 in
      let ind = 32 * m_ind + n_ind in
      let th1 = Array.get add_clauses ind
      and fl = Array.get add_flags ind in
      match fl with
        0 -> INST [m_hi,m_tm] th1
      | 1 -> INST [n_hi,n_tm] th1
      | 2 -> let th2 = NUM_ADD_RULE m_hi n_hi in
             (match concl th2 with Comb(_,ptm) ->
              let th3 = INST [m_hi,m_tm; n_hi,n_tm;ptm,p_tm] th1 in
              EQ_MP th3 th2)
      | 3 -> let th2 = NUM_ADC_RULE m_hi n_hi in
             (match concl th2 with Comb(_,ptm) ->
              let th3 = INST [m_hi,m_tm; n_hi,n_tm;ptm,p_tm] th1 in
              EQ_MP th3 th2)
    and NUM_ADC_RULE mtm ntm =
      let m_lo,m_hi = topsplit mtm
      and n_lo,n_hi = topsplit ntm in
      let m_ind = if m_hi = zero_tm then m_lo else m_lo + 16
      and n_ind = if n_hi = zero_tm then n_lo else n_lo + 16 in
      let ind = 32 * m_ind + n_ind in
      let th1 = Array.get adc_clauses ind
      and fl = Array.get adc_flags ind in
      match fl with
        0 -> INST [m_hi,m_tm] th1
      | 1 -> INST [n_hi,n_tm] th1
      | 2 -> let th2 = NUM_ADD_RULE m_hi n_hi in
             (match concl th2 with Comb(_,ptm) ->
              let th3 = INST [m_hi,m_tm; n_hi,n_tm;ptm,p_tm] th1 in
              EQ_MP th3 th2)
      | 3 -> let th2 = NUM_ADC_RULE m_hi n_hi in
             (match concl th2 with Comb(_,ptm) ->
              let th3 = INST [m_hi,m_tm; n_hi,n_tm;ptm,p_tm] th1 in
              EQ_MP th3 th2) in
    NUM_ADD_RULE,NUM_ADC_RULE in
  let NUM_SHIFT_CONV =
    let pth_0 = (STANDARDIZE o prove)
     (`(n = a + p * b <=> BIT0 n = BIT0 a + BIT0 p * b)`,
      REWRITE_TAC[BIT0; BIT1] THEN
      REWRITE_TAC[GSYM MULT_2; GSYM MULT_ASSOC; GSYM LEFT_ADD_DISTRIB] THEN
      REWRITE_TAC[EQ_MULT_LCANCEL; ARITH_EQ])
    and pth_z = (STANDARDIZE o prove)
     (`n = _0 + p * b <=> BIT0 n = _0 + BIT0 p * b`,
      SUBST1_TAC(SYM(SPEC `_0` NUMERAL)) THEN
      REWRITE_TAC[BIT1; BIT0] THEN
      REWRITE_TAC[ADD_CLAUSES; GSYM MULT_2] THEN
      REWRITE_TAC[GSYM MULT_ASSOC; EQ_MULT_LCANCEL; ARITH_EQ])
    and pth_1 = (STANDARDIZE o prove)
     (`(n = a + p * b <=> BIT1 n = BIT1 a + BIT0 p * b)`,
      REWRITE_TAC[BIT0; BIT1] THEN
      REWRITE_TAC[GSYM MULT_2; GSYM MULT_ASSOC; GSYM LEFT_ADD_DISTRIB;
                  ADD_CLAUSES; SUC_INJ] THEN
      REWRITE_TAC[EQ_MULT_LCANCEL; ARITH_EQ])
    and pth_base = (STANDARDIZE o prove)
     (`n = _0 + BIT1 _0 * n`,
      MESON_TAC[ADD_CLAUSES; MULT_CLAUSES; NUMERAL])
    and pth_triv = (STANDARDIZE o prove)
     (`_0 = a + p * b <=> _0 = a + BIT0 p * b`,
      CONV_TAC(BINOP_CONV SYM_CONV) THEN
      SUBST1_TAC(SYM(SPEC `_0` NUMERAL)) THEN
      REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; BIT0])
    and pths_1 = (Array.of_list o CONJUNCTS o STANDARDIZE o prove)
     (`(n = a + p * b <=>
        BIT0(BIT0(BIT0(BIT0 n))) =
        BIT0(BIT0(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT1(BIT0(BIT0(BIT0 n))) =
        BIT1(BIT0(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT0(BIT1(BIT0(BIT0 n))) =
        BIT0(BIT1(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT1(BIT1(BIT0(BIT0 n))) =
        BIT1(BIT1(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT0(BIT0(BIT1(BIT0 n))) =
        BIT0(BIT0(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT1(BIT0(BIT1(BIT0 n))) =
        BIT1(BIT0(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT0(BIT1(BIT1(BIT0 n))) =
        BIT0(BIT1(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT1(BIT1(BIT1(BIT0 n))) =
        BIT1(BIT1(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT0(BIT0(BIT0(BIT1 n))) =
        BIT0(BIT0(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT1(BIT0(BIT0(BIT1 n))) =
        BIT1(BIT0(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT0(BIT1(BIT0(BIT1 n))) =
        BIT0(BIT1(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT1(BIT1(BIT0(BIT1 n))) =
        BIT1(BIT1(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT0(BIT0(BIT1(BIT1 n))) =
        BIT0(BIT0(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT1(BIT0(BIT1(BIT1 n))) =
        BIT1(BIT0(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT0(BIT1(BIT1(BIT1 n))) =
        BIT0(BIT1(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT1(BIT1(BIT1(BIT1 n))) =
        BIT1(BIT1(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b)`,
      MP_TAC(REWRITE_RULE[GSYM MULT_2] BIT0) THEN
      MP_TAC(REWRITE_RULE[GSYM MULT_2] BIT1) THEN
      ABBREV_TAC `two = 2` THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[ADD_CLAUSES; SUC_INJ; EQ_MULT_LCANCEL; ARITH_EQ;
                  GSYM LEFT_ADD_DISTRIB; GSYM MULT_ASSOC])
    and pths_0 = (Array.of_list o CONJUNCTS o STANDARDIZE o prove)
     (`(n = _0 + p * b <=>
        BIT0(BIT0(BIT0(BIT0 n))) =
        _0 + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT1(BIT0(BIT0(BIT0 n))) =
        BIT1 _0 + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT0(BIT1(BIT0(BIT0 n))) =
        BIT0(BIT1 _0) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT1(BIT1(BIT0(BIT0 n))) =
        BIT1(BIT1 _0) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT0(BIT0(BIT1(BIT0 n))) =
        BIT0(BIT0(BIT1 _0)) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT1(BIT0(BIT1(BIT0 n))) =
        BIT1(BIT0(BIT1 _0)) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT0(BIT1(BIT1(BIT0 n))) =
        BIT0(BIT1(BIT1 _0)) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT1(BIT1(BIT1(BIT0 n))) =
        BIT1(BIT1(BIT1 _0)) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT0(BIT0(BIT0(BIT1 n))) =
        BIT0(BIT0(BIT0(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT1(BIT0(BIT0(BIT1 n))) =
        BIT1(BIT0(BIT0(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT0(BIT1(BIT0(BIT1 n))) =
        BIT0(BIT1(BIT0(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT1(BIT1(BIT0(BIT1 n))) =
        BIT1(BIT1(BIT0(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT0(BIT0(BIT1(BIT1 n))) =
        BIT0(BIT0(BIT1(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT1(BIT0(BIT1(BIT1 n))) =
        BIT1(BIT0(BIT1(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT0(BIT1(BIT1(BIT1 n))) =
        BIT0(BIT1(BIT1(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT1(BIT1(BIT1(BIT1 n))) =
        BIT1(BIT1(BIT1(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b)`,
      SUBST1_TAC(MESON[NUMERAL] `_0 = 0`) THEN
      MP_TAC(REWRITE_RULE[GSYM MULT_2] BIT0) THEN
      MP_TAC(REWRITE_RULE[GSYM MULT_2] BIT1) THEN
      ABBREV_TAC `two = 2` THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[ADD_CLAUSES; SUC_INJ; EQ_MULT_LCANCEL; ARITH_EQ;
                  GSYM LEFT_ADD_DISTRIB; GSYM MULT_ASSOC]) in
    let rec NUM_SHIFT_CONV k tm =
      if k <= 0 then INST [tm,n_tm] pth_base else
      match tm with
        Comb(_,Comb(_,Comb(_,Comb(_,_)))) when k >= 4 ->
          let i,ntm = topsplit tm in
          let th1 = NUM_SHIFT_CONV (k - 4) ntm in
          (match concl th1 with
               Comb(_,Comb(Comb(_,Const("_0",_)),Comb(Comb(_,ptm),btm))) ->
                  let th2 = Array.get pths_0 i in
                  let th3 = INST [ntm,n_tm; btm,b_tm; ptm,p_tm] th2 in
                  EQ_MP th3 th1
             | Comb(_,Comb(Comb(_,atm),Comb(Comb(_,ptm),btm))) ->
                  let th2 = Array.get pths_1 i in
                  let th3 = INST[ntm,n_tm; atm,a_tm; btm,b_tm; ptm,p_tm] th2 in
                  EQ_MP th3 th1)
      | Comb(Const("BIT0",_),ntm) ->
            let th1 = NUM_SHIFT_CONV (k - 1) ntm in
            (match concl th1 with
               Comb(_,Comb(Comb(_,Const("_0",_)),Comb(Comb(_,ptm),btm))) ->
                 EQ_MP (INST [ntm,n_tm; btm,b_tm; ptm,p_tm] pth_z) th1
             | Comb(_,Comb(Comb(_,atm),Comb(Comb(_,ptm),btm))) ->
                 EQ_MP
                  (INST[ntm,n_tm; atm,a_tm; btm,b_tm; ptm,p_tm] pth_0) th1)
      | Comb(Const("BIT1",_),ntm) ->
            let th1 = NUM_SHIFT_CONV (k - 1) ntm in
            (match concl th1 with
               Comb(_,Comb(Comb(_,atm),Comb(Comb(_,ptm),btm))) ->
                 EQ_MP
                  (INST [ntm,n_tm; atm,a_tm; btm,b_tm; ptm,p_tm] pth_1) th1)
      | Const("_0",_) ->
            let th1 = NUM_SHIFT_CONV (k - 1) tm in
            (match concl th1 with
               Comb(_,Comb(Comb(_,atm),Comb(Comb(_,ptm),btm))) ->
                 EQ_MP (INST [atm,a_tm; btm,b_tm; ptm,p_tm] pth_triv)
                       th1)
      | _ -> failwith "malformed numeral" in
    NUM_SHIFT_CONV in
  let NUM_UNSHIFT_CONV =
    let pth_triv = (STANDARDIZE o prove)
     (`a + p * _0 = a`,
      SUBST1_TAC(SYM(SPEC `_0` NUMERAL)) THEN
      REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES])
    and pth_base = (STANDARDIZE o prove)
     (`a + BIT1 _0 * b = a + b`,
      SUBST1_TAC(SYM(SPEC `BIT1 _0` NUMERAL)) THEN
      REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES])
    and pth_0 = (STANDARDIZE o prove)
     (`BIT0 a + BIT0 p * b = BIT0(a + p * b)`,
      REWRITE_TAC[BIT0] THEN REWRITE_TAC[GSYM MULT_2] THEN
      REWRITE_TAC[GSYM MULT_ASSOC; GSYM LEFT_ADD_DISTRIB])
    and pth_1 = (STANDARDIZE o prove)
     (`BIT1 a + BIT0 p * b = BIT1(a + p * b)`,
      REWRITE_TAC[BIT0; BIT1] THEN REWRITE_TAC[GSYM MULT_2] THEN
      REWRITE_TAC[ADD_CLAUSES; SUC_INJ] THEN
      REWRITE_TAC[GSYM MULT_ASSOC; GSYM LEFT_ADD_DISTRIB] THEN
      REWRITE_TAC[EQ_MULT_LCANCEL; ARITH_EQ])
    and pth_z = (STANDARDIZE o prove)
     (`_0 + BIT0 p * b = BIT0(_0 + p * b)`,
      SUBST1_TAC(SYM(SPEC `_0` NUMERAL)) THEN
      REWRITE_TAC[BIT1; BIT0] THEN REWRITE_TAC[ADD_CLAUSES] THEN
      REWRITE_TAC[RIGHT_ADD_DISTRIB])
    and puths_1 = (Array.of_list o CONJUNCTS o STANDARDIZE o prove)
       (`(a + p * b = n <=>
          BIT0(BIT0(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT0(BIT0(BIT0(BIT0 n)))) /\
         (a + p * b = n <=>
          BIT1(BIT0(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT1(BIT0(BIT0(BIT0 n)))) /\
         (a + p * b = n <=>
          BIT0(BIT1(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT0(BIT1(BIT0(BIT0 n)))) /\
         (a + p * b = n <=>
          BIT1(BIT1(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT1(BIT1(BIT0(BIT0 n)))) /\
         (a + p * b = n <=>
          BIT0(BIT0(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT0(BIT0(BIT1(BIT0 n)))) /\
         (a + p * b = n <=>
          BIT1(BIT0(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT1(BIT0(BIT1(BIT0 n)))) /\
         (a + p * b = n <=>
          BIT0(BIT1(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT0(BIT1(BIT1(BIT0 n)))) /\
         (a + p * b = n <=>
          BIT1(BIT1(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT1(BIT1(BIT1(BIT0 n)))) /\
         (a + p * b = n <=>
          BIT0(BIT0(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT0(BIT0(BIT0(BIT1 n)))) /\
         (a + p * b = n <=>
          BIT1(BIT0(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT1(BIT0(BIT0(BIT1 n)))) /\
         (a + p * b = n <=>
          BIT0(BIT1(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT0(BIT1(BIT0(BIT1 n)))) /\
         (a + p * b = n <=>
          BIT1(BIT1(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT1(BIT1(BIT0(BIT1 n)))) /\
         (a + p * b = n <=>
          BIT0(BIT0(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT0(BIT0(BIT1(BIT1 n)))) /\
         (a + p * b = n <=>
          BIT1(BIT0(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT1(BIT0(BIT1(BIT1 n)))) /\
         (a + p * b = n <=>
          BIT0(BIT1(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT0(BIT1(BIT1(BIT1 n)))) /\
         (a + p * b = n <=>
          BIT1(BIT1(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT1(BIT1(BIT1(BIT1 n))))`,
      SUBST1_TAC(MESON[NUMERAL] `_0 = 0`) THEN
      MP_TAC(REWRITE_RULE[GSYM MULT_2] BIT0) THEN
      MP_TAC(REWRITE_RULE[GSYM MULT_2] BIT1) THEN
      ABBREV_TAC `two = 2` THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[ADD_CLAUSES; SUC_INJ; EQ_MULT_LCANCEL; ARITH_EQ;
                  GSYM LEFT_ADD_DISTRIB; GSYM MULT_ASSOC]) in
    let puths_2 = Array.of_list
     (map (fun i -> let th1 = Array.get puths_1 (i mod 16)
                    and th2 = Array.get puths_1 (i / 16) in
                    let th3 = GEN_REWRITE_RULE RAND_CONV [th1] th2 in
                    STANDARDIZE th3) (0--255)) in
    let rec NUM_UNSHIFT_CONV tm =
      match tm with
        Comb(Comb(Const("+",_),atm),Comb(Comb(Const("*",_),ptm),btm)) ->
         (match (atm,ptm,btm) with
            (_,_,Const("_0",_)) ->
                INST [atm,a_tm; ptm,p_tm] pth_triv
          | (_,Comb(Const("BIT1",_),Const("_0",_)),_) ->
                let th1 = INST [atm,a_tm; btm,b_tm] pth_base in
                let Comb(_,Comb(Comb(_,mtm),ntm)) = concl th1 in
                TRANS th1 (NUM_ADD_RULE mtm ntm)
          | (Comb(_,Comb(_,Comb(_,Comb(_,atm')))),
              Comb(_,Comb(_,Comb(_,Comb(_,(Comb(_,_) as ptm'))))),_) ->
                let i,_ = topsplit atm in
                (match (atm',ptm') with
                   (Comb(_,Comb(_,Comb(_,Comb(_,atm'')))),
                      Comb(_,Comb(_,Comb(_,Comb(_,(Comb(_,_) as ptm'')))))) ->
                     let j,_ = topsplit atm' in
                     let tm' = mk_comb(mk_comb(add_tm,atm''),
                                       mk_comb(mk_comb(mul_tm,ptm''),btm)) in
                     let th1 = NUM_UNSHIFT_CONV tm' in
                     let th2 = INST [atm'',a_tm; ptm'',p_tm; btm,b_tm;
                                     rand(concl th1),n_tm]
                                    (Array.get puths_2 (16 * j + i)) in
                     EQ_MP th2 th1
                 | _ ->
                   let tm' = mk_comb(mk_comb(add_tm,atm'),
                                     mk_comb(mk_comb(mul_tm,ptm'),btm)) in
                   let th1 = NUM_UNSHIFT_CONV tm' in
                   let th2 = INST [atm',a_tm; ptm',p_tm; btm,b_tm;
                                   rand(concl th1),n_tm]
                                  (Array.get puths_1 i) in
                   EQ_MP th2 th1)
          | (Const("_0",_),Comb(Const("BIT0",_),qtm),_) ->
                let th1 = INST [btm,b_tm; qtm,p_tm] pth_z in
                CONV_RULE(RAND_CONV(RAND_CONV NUM_UNSHIFT_CONV)) th1
          | (Comb(Const("BIT0",_),ctm),Comb(Const("BIT0",_),qtm),_) ->
                let th1 = INST [ctm,a_tm; btm,b_tm; qtm,p_tm] pth_0 in
                CONV_RULE(RAND_CONV(RAND_CONV NUM_UNSHIFT_CONV)) th1
          | (Comb(Const("BIT1",_),ctm),Comb(Const("BIT0",_),qtm),_) ->
                let th1 = INST [ctm,a_tm; btm,b_tm; qtm,p_tm] pth_1 in
                CONV_RULE(RAND_CONV(RAND_CONV NUM_UNSHIFT_CONV)) th1
          | _ -> failwith "malformed numeral")
      | _ -> failwith "malformed numeral" in
    NUM_UNSHIFT_CONV in
  let NUM_SQUARE_RULE =
    let pth_0 = (STANDARDIZE o prove)
     (`_0 EXP 2 = _0`,
      MESON_TAC[NUMERAL; REWRITE_CONV[ARITH] `0 EXP 2`])
    and pth_1 = (STANDARDIZE o prove)
     (`(BIT1 _0) EXP 2 = BIT1 _0`,
      MESON_TAC[NUMERAL; REWRITE_CONV[ARITH] `1 EXP 2`])
    and pth_even = (STANDARDIZE o prove)
     (`m EXP 2 = n <=> (BIT0 m) EXP 2 = BIT0(BIT0 n)`,
      ABBREV_TAC `two = 2` THEN
      REWRITE_TAC[BIT0] THEN EXPAND_TAC "two" THEN
      REWRITE_TAC[GSYM MULT_2] THEN REWRITE_TAC[EXP_2] THEN
      REWRITE_TAC[AC MULT_AC `(2 * m) * (2 * n) = 2 * 2 * m * n`] THEN
      REWRITE_TAC[EQ_MULT_LCANCEL; ARITH_EQ])
    and pth_odd = (STANDARDIZE o prove)
     (`m EXP 2 = n <=> (BIT1 m) EXP 2 = BIT1(BIT0(m + n))`,
      ABBREV_TAC `two = 2` THEN
      REWRITE_TAC[NUMERAL; BIT0; BIT1] THEN
      EXPAND_TAC "two" THEN REWRITE_TAC[GSYM MULT_2] THEN
      REWRITE_TAC[EXP_2; MULT_CLAUSES; ADD_CLAUSES] THEN
      REWRITE_TAC[SUC_INJ; GSYM MULT_ASSOC; GSYM LEFT_ADD_DISTRIB] THEN
      REWRITE_TAC[AC ADD_AC `(m + m * 2 * m) + m = m * 2 * m + m + m`] THEN
      REWRITE_TAC[GSYM MULT_2; AC MULT_AC `m * 2 * m = 2 * m * m`] THEN
      REWRITE_TAC[GSYM MULT_ASSOC; GSYM LEFT_ADD_DISTRIB] THEN
      REWRITE_TAC[EQ_MULT_LCANCEL; ARITH_EQ] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ADD_SYM] THEN
      REWRITE_TAC[EQ_ADD_RCANCEL])
    and pth_qstep = (UNDISCH o STANDARDIZE o prove)
     (`n + BIT1 _0 = m /\
       m EXP 2 = p /\
       m + a = BIT0(BIT0 p)
       ==> (BIT1(BIT1(BIT1 n))) EXP 2 = BIT1(BIT0(BIT0(BIT0 a)))`,
      ABBREV_TAC `two = 2` THEN
      SUBST1_TAC(MESON[NUMERAL] `_0 = 0`) THEN
      REWRITE_TAC[BIT1; BIT0] THEN EXPAND_TAC "two" THEN
      REWRITE_TAC[GSYM MULT_2] THEN
      REWRITE_TAC[ADD1; LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
      REWRITE_TAC[MULT_ASSOC] THEN REWRITE_TAC[ARITH] THEN
      REWRITE_TAC[IMP_CONJ] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
      MATCH_MP_TAC(MESON[EQ_ADD_LCANCEL]
       `!m:num. m + n = m + p ==> n = p`) THEN
      EXISTS_TAC `16 * (n + 1)` THEN
      ASM_REWRITE_TAC[ADD_ASSOC; GSYM LEFT_ADD_DISTRIB] THEN
      EXPAND_TAC "two" THEN REWRITE_TAC[EXP_2] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN
      REWRITE_TAC[MULT_CLAUSES; MULT_ASSOC] THEN
      REWRITE_TAC[AC MULT_AC `(8 * n) * NUMERAL p = (8 * NUMERAL p) * n`] THEN
      REWRITE_TAC[ARITH] THEN
      REWRITE_TAC[AC ADD_AC
         `(n + 16) + p + q + 49 = (n + p + q) + (16 + 49)`] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN REWRITE_TAC[ARITH] THEN
      REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
      REWRITE_TAC[GSYM ADD_ASSOC; GSYM MULT_2; MULT_ASSOC] THEN
      ONCE_REWRITE_TAC[AC ADD_AC `a + b + c:num = b + a + c`] THEN
      REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB] THEN
      REWRITE_TAC[ARITH])
    and pth_rec = (UNDISCH o STANDARDIZE o prove)
     (`n = l + p * h /\
       h + l = m /\
       h EXP 2 = a /\
       l EXP 2 = c /\
       m EXP 2 = d /\
       a + c = e /\
       e + b = d
       ==> n EXP 2 = c + p * (b + p * a)`,
      REWRITE_TAC[IMP_CONJ] THEN
      DISCH_THEN SUBST1_TAC THEN
      REPLICATE_TAC 5 (DISCH_THEN(SUBST1_TAC o SYM)) THEN
      REWRITE_TAC[EXP_2; LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN
      REWRITE_TAC[MULT_AC] THEN CONV_TAC(BINOP_CONV NUM_CANCEL_CONV) THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN
      REWRITE_TAC[MULT_AC] THEN REWRITE_TAC[ADD_AC])
    and pth_toom3 = (STANDARDIZE o prove)
     (`h EXP 2 = e /\
       l EXP 2 = a /\
       (l + BIT1 _0 * (m + BIT1 _0 * h)) EXP 2 =
       a +  BIT1 _0 * (b +  BIT1 _0 * (c +  BIT1 _0 * (d +  BIT1 _0 * e))) /\
       (l + BIT0(BIT1 _0) * (m + BIT0(BIT1 _0) * h)) EXP 2 =
       a + BIT0(BIT1 _0) * (b + BIT0(BIT1 _0) *
       (c + BIT0(BIT1 _0) * (d + BIT0(BIT1 _0) * e))) /\
       (h + BIT0(BIT1 _0) * (m + BIT0(BIT1 _0) * l)) EXP 2 =
       e + BIT0(BIT1 _0) * (d + BIT0(BIT1 _0) *
       (c + BIT0(BIT1 _0) * (b + BIT0(BIT1 _0) * a)))
       ==> (l + p * (m + p * h)) EXP 2 =
           a + p * (b + p * (c + p * (d + p * e)))`,
      ABBREV_TAC `two = 2` THEN
      SUBST1_TAC(MESON[NUMERAL] `_0 = 0`) THEN
      REWRITE_TAC[BIT1; BIT0] THEN
      EXPAND_TAC "two" THEN REWRITE_TAC[GSYM MULT_2] THEN
      REWRITE_TAC[ARITH] THEN
      SUBGOAL_THEN
       `!p x y z. (x + p * (y + p * z)) EXP 2 =
                  x * x + p * (2 * x * y + p * ((2 * x * z + y * y) +
                            p * (2 * y * z + p * z * z)))`
       (fun th -> REWRITE_TAC[th])
      THENL
       [REWRITE_TAC[EXP_2; MULT_2; LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN
        REWRITE_TAC[MULT_AC] THEN REWRITE_TAC[ADD_AC];
        REWRITE_TAC[EXP_2]] THEN
      MAP_EVERY ABBREV_TAC
       [`a':num = l * l`;  `b' = 2 * l * m`; `c' = 2 * l * h + m * m`;
        `d' = 2 * m * h`; `e':num = h * h`] THEN
      SUBST1_TAC(AC MULT_AC `2 * m * l = 2 * l * m`) THEN
      SUBST1_TAC(AC MULT_AC `2 * h * l = 2 * l * h`) THEN
      SUBST1_TAC(AC MULT_AC `2 * h * m = 2 * m * h`) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "two" THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      ASM_CASES_TAC `a':num = a` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `e':num = e` THEN ASM_REWRITE_TAC[] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      REWRITE_TAC[EQ_ADD_LCANCEL; EQ_MULT_LCANCEL] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
      REWRITE_TAC[ARITH] THEN
      REWRITE_TAC[MULT_CLAUSES; EQ_ADD_LCANCEL] THEN
      REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[]
       `b = b' /\ c = c' /\ d = d'
        ==> 5 * b + c' + d' = 5 * b' + c + d`)) THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
      REWRITE_TAC(map (fun k ->
          SYM(REWRITE_CONV[ARITH_SUC]
          (mk_comb(suc_tm,mk_small_numeral(k - 1)))))
         (1--5)) THEN
      REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
      CONV_TAC(LAND_CONV NUM_CANCEL_CONV) THEN DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[]
       `b = b' /\ c = c' /\ d = d'
        ==> b + d':num = b' + d /\ 4 * b + d' = 4 * b' + d`)) THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
      REWRITE_TAC(map (fun k ->
          SYM(REWRITE_CONV[ARITH_SUC]
          (mk_comb(suc_tm,mk_small_numeral(k - 1)))))
         (1--4)) THEN
      REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
      CONV_TAC(LAND_CONV(BINOP_CONV NUM_CANCEL_CONV)) THEN
      REWRITE_TAC[GSYM MULT_2] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[GSYM(el 4 (CONJUNCTS MULT_CLAUSES))] THEN
      SIMP_TAC[EQ_MULT_LCANCEL; NOT_SUC])
    and pth_even3 = (STANDARDIZE o prove)
     (`m EXP 2 = n <=>
       (BIT0(BIT0(BIT0 m))) EXP 2 = BIT0(BIT0(BIT0(BIT0(BIT0(BIT0 n)))))`,
      ABBREV_TAC `two = 2` THEN
      REWRITE_TAC[BIT0] THEN REWRITE_TAC[GSYM MULT_2] THEN
      EXPAND_TAC "two" THEN REWRITE_TAC[EXP_2] THEN
      REWRITE_TAC[AC MULT_AC
       `(2 * 2 * 2 * m) * 2 * 2 * 2 * m = 2 * 2 * 2 * 2 * 2 * 2 * m * m`] THEN
      REWRITE_TAC[EQ_MULT_LCANCEL; ARITH_EQ]) in
    let NUM_UNSHIFT2_CONV =
      RAND_CONV(RAND_CONV NUM_UNSHIFT_CONV) THENC NUM_UNSHIFT_CONV in
    let NUM_UNSHIFT3_CONV =
      RAND_CONV(RAND_CONV NUM_UNSHIFT2_CONV) THENC NUM_UNSHIFT_CONV in
    let NUM_UNSHIFT4_CONV =
      RAND_CONV(RAND_CONV NUM_UNSHIFT3_CONV) THENC NUM_UNSHIFT_CONV in
    let BINOP2_CONV conv1 conv2 = COMB2_CONV (RAND_CONV conv1) conv2 in
    let TOOM3_CONV = BINOP2_CONV
      (LAND_CONV NUM_UNSHIFT2_CONV) NUM_UNSHIFT4_CONV in
    let rec GEN_NUM_SQUARE_RULE w z tm =
      match tm with
        Const("_0",_) -> pth_0
      | Comb(Const("BIT0",_),mtm) ->
           (match mtm with
              Comb(Const("BIT0",_),Comb(Const("BIT0",_),ptm)) ->
                 let th1 = GEN_NUM_SQUARE_RULE w (z - 3) ptm in
                 let ntm = rand(concl th1) in
                 EQ_MP (INST [ptm,m_tm; ntm,n_tm] pth_even3) th1
            | _ ->
                 let th1 = GEN_NUM_SQUARE_RULE w (z - 1) mtm in
                 let ntm = rand(concl th1) in
                 EQ_MP (INST [mtm,m_tm; ntm,n_tm] pth_even) th1)
      | Comb(Const("BIT1",_),mtm) ->
            if mtm = zero_tm then pth_1 else
            if (w < 100 || z < 20) && w + z < 150 then
              match mtm with
                Comb(Const("BIT1",_),Comb(Const("BIT1",_),ntm)) ->
                    let th1 = NUM_ADD_RULE ntm one_tm in
                    let mtm = rand(concl th1) in
                    let th2 = NUM_SQUARE_RULE mtm in
                    let ptm = rand(concl th2) in
                    let atm = subbn
                      (mk_comb(BIT0_tm,mk_comb(BIT0_tm,ptm))) mtm in
                    let th3 = NUM_ADD_RULE mtm atm in
                    let th4 = INST
                      [atm,a_tm; mtm,m_tm; ntm,n_tm; ptm,p_tm] pth_qstep in
                    QUICK_PROVE_HYP (CONJ th1 (CONJ th2 th3)) th4
              | _ ->
                    let th1 = GEN_NUM_SQUARE_RULE (w - 1) z mtm in
                    let ntm = rand(concl th1) in
                    let th2 = EQ_MP (INST [mtm,m_tm; ntm,n_tm] pth_odd) th1 in
                    (match concl th2 with
                      Comb(_,Comb(_,Comb(_,Comb(Comb(_,ptm),qtm)))) ->
                        let th3 = NUM_ADD_RULE ptm qtm in
                        TRANS th2 (AP_BIT1 (AP_BIT0 th3)))
            else if w + z < 800 then
              let k2 = (w + z) / 2 in
              let th1 = NUM_SHIFT_CONV k2 tm in
              let Comb(Comb(_,ltm),Comb(Comb(_,ptm),htm)) = rand(concl th1) in
              let th2 = NUM_ADD_RULE htm ltm in
              let mtm = rand(concl th2) in
              let th3 = NUM_SQUARE_RULE htm
              and th4 = NUM_SQUARE_RULE ltm
              and th5 = NUM_SQUARE_RULE mtm in
              let atm = rand(concl th3)
              and ctm = rand(concl th4)
              and dtm = rand(concl th5) in
              let th6 = NUM_ADD_RULE atm ctm in
              let etm = rand(concl th6) in
              let btm = subbn dtm etm in
              let th7 = NUM_ADD_RULE etm btm in
              let dtm = rand(concl th7) in
              let th8 = INST [atm,a_tm; btm,b_tm; ctm,c_tm; dtm,d_tm; etm,e_tm;
                              htm,h_tm; ltm,l_tm; mtm,m_tm; tm,n_tm; ptm,p_tm]
                        pth_rec in
              let th9 = QUICK_PROVE_HYP (end_itlist CONJ
                   [th1;th2;th3;th4;th5;th6;th7]) th8 in
              CONV_RULE(RAND_CONV(RAND_CONV(RAND_CONV NUM_UNSHIFT_CONV) THENC
                                  NUM_UNSHIFT_CONV)) th9
            else
              let k3 = (w + z) / 3 in
              let th0 = (NUM_SHIFT_CONV k3 THENC
                         RAND_CONV(RAND_CONV(NUM_SHIFT_CONV k3))) tm in
              let Comb(Comb(_,ltm),Comb(Comb(_,ptm),
                   Comb(Comb(_,mtm),Comb(Comb(_,_),htm)))) = rand(concl th0) in
              let th1 = NUM_SQUARE_RULE htm
              and th2 = NUM_SQUARE_RULE ltm in
              let atm = rand(concl th2) and etm = rand(concl th1) in
              let lnum = dest_raw_numeral ltm
              and mnum = dest_raw_numeral mtm
              and hnum = dest_raw_numeral htm in
              let btm = rand(mk_numeral(num_2 */ lnum */ mnum))
              and ctm = rand(mk_numeral(mnum */ mnum +/ num_2 */ lnum */ hnum))
              and dtm = rand(mk_numeral(num_2 */ hnum */ mnum)) in
              let th = INST
                [atm,a_tm; btm,b_tm; ctm,c_tm; dtm,d_tm; etm,e_tm;
                 htm,h_tm; mtm,m_tm; ltm,l_tm; ptm,p_tm] pth_toom3 in
              let th' = CONV_RULE
               (BINOP2_CONV
                (RAND_CONV(RAND_CONV
                 (BINOP2_CONV TOOM3_CONV (BINOP2_CONV TOOM3_CONV TOOM3_CONV))))
                TOOM3_CONV) th in
              let [tm3;tm4;tm5] = conjuncts(rand(rand(lhand(concl th')))) in
              let th3 = NUM_SQUARE_RULE (lhand(lhand tm3))
              and th4 = NUM_SQUARE_RULE (lhand(lhand tm4))
              and th5 = NUM_SQUARE_RULE (lhand(lhand tm5)) in
              MP th' (end_itlist CONJ [th1;th2;th3;th4;th5])
    and NUM_SQUARE_RULE tm =
      let w,z = bitcounts tm in GEN_NUM_SQUARE_RULE w z tm in
    NUM_SQUARE_RULE in
  let NUM_MUL_RULE =
    let QUICK_PROVE_HYP ath bth =
      EQ_MP (DEDUCT_ANTISYM_RULE ath bth) ath
    and pth_0l,pth_0r = (CONJ_PAIR o STANDARDIZE o prove)
     (`_0 * n = _0 /\ m * _0 = _0`,
      MESON_TAC[NUMERAL; MULT_CLAUSES])
    and pth_1l,pth_1r = (CONJ_PAIR o STANDARDIZE o prove)
     (`(BIT1 _0) * n = n /\ m * (BIT1 _0) = m`,
      MESON_TAC[NUMERAL; MULT_CLAUSES])
    and pth_evenl,pth_evenr = (CONJ_PAIR o STANDARDIZE o prove)
     (`(m * n = p <=> (BIT0 m) * n = BIT0 p) /\
       (m * n = p <=> m * BIT0 n = BIT0 p)`,
      REWRITE_TAC[BIT0] THEN REWRITE_TAC[GSYM MULT_2] THEN
      REWRITE_TAC[AC MULT_AC `m * 2 * n = 2 * m * n`] THEN
      REWRITE_TAC[GSYM MULT_ASSOC; EQ_MULT_LCANCEL; ARITH_EQ])
    and pth_oddl,pth_oddr = (CONJ_PAIR o STANDARDIZE o prove)
     (`(m * n = p <=> BIT1 m * n = BIT0 p + n) /\
       (m * n = p <=> m * BIT1 n = BIT0 p + m)`,
      REWRITE_TAC[BIT0; BIT1] THEN REWRITE_TAC[GSYM MULT_2] THEN
      REWRITE_TAC[MULT_CLAUSES] THEN
      REWRITE_TAC[MESON[MULT_AC; ADD_SYM] `m + m * 2 * n = 2 * m * n + m`] THEN
      REWRITE_TAC[GSYM MULT_ASSOC; EQ_MULT_LCANCEL; EQ_ADD_RCANCEL] THEN
      REWRITE_TAC[ARITH_EQ]) in
    let pth_oo1 = (UNDISCH_ALL o STANDARDIZE o prove)
     (`n + p = m /\ SUC(m + n) = a /\ p EXP 2 = b /\ a EXP 2 = c /\ b + d = c
        ==> ((BIT1 m) * (BIT1 n) = d)`,
      ABBREV_TAC `two = 2` THEN REWRITE_TAC[BIT1; IMP_CONJ] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[EXP_2; GSYM MULT_2] THEN
      REPLICATE_TAC 4 (DISCH_THEN(SUBST1_TAC o SYM)) THEN
      REWRITE_TAC[ADD1; AC ADD_AC `((n + p) + n) + 1 = (p + (n + n)) + 1`] THEN
      REWRITE_TAC[GSYM MULT_2] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN
      REWRITE_TAC[GSYM ADD_ASSOC; MULT_CLAUSES; EQ_ADD_LCANCEL] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[MULT_2; LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN
      REWRITE_TAC[MULT_AC] THEN REWRITE_TAC[ADD_AC]) in
    let pth_oo2 = PURE_ONCE_REWRITE_RULE[MULT_SYM]
                   (INST [n_tm,m_tm; m_tm,n_tm] pth_oo1) in
    let pth_recodel = (UNDISCH_ALL o STANDARDIZE o prove)
     (`SUC(_0 + m) = p ==> (p * n = a + n <=> m * n = a)`,
      SUBST1_TAC(MESON[NUMERAL] `_0 = 0`) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; EQ_ADD_RCANCEL])
    and pth_recoder = (UNDISCH_ALL o STANDARDIZE o prove)
     (`SUC(_0 + n) = p ==> (m * p = a + m <=> m * n = a)`,
      ONCE_REWRITE_TAC[MULT_SYM] THEN
      SUBST1_TAC(MESON[NUMERAL] `_0 = 0`) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; EQ_ADD_RCANCEL]) in
    let rec NUM_MUL_RULE k l tm tm' =
      match (tm,tm') with
        (Const("_0",_),_) -> INST [tm',n_tm] pth_0l
      | (_,Const("_0",_)) -> INST [tm,m_tm] pth_0r
      | (Comb(Const("BIT1",_),Const("_0",_)),_) -> INST [tm',n_tm] pth_1l
      | (_,Comb(Const("BIT1",_),Const("_0",_))) -> INST [tm,m_tm] pth_1r
      | (Comb(Const("BIT0",_),mtm),_) ->
            let th0 = NUM_MUL_RULE (k - 1) l mtm tm' in
            let th1 = INST
             [mtm,m_tm; tm',n_tm; rand(concl th0),p_tm] pth_evenl in
            EQ_MP th1 th0
      | (_,Comb(Const("BIT0",_),ntm)) ->
            let th0 = NUM_MUL_RULE k (l - 1) tm ntm in
            let th1 = INST
             [tm,m_tm; ntm,n_tm; rand(concl th0),p_tm] pth_evenr in
            EQ_MP th1 th0
      | (Comb(Const("BIT1",_),mtm),Comb(Const("BIT1",_),ntm)) ->
          if k <= 50 || l <= 50 ||
             num k */ num k <=/ num l ||
             num l */ num l <=/ num k then
            match (mtm,ntm) with
              (Comb(Const("BIT1",_),Comb(Const("BIT1",_),_)),_) ->
                 let th1 = NUM_ADC_RULE zero_tm tm in
                 let ptm = rand(concl th1) in
                 let th2 = NUM_MUL_RULE k l ptm tm' in
                 let atm = subbn (rand(concl th2)) tm' in
                 let th3 = INST [tm,m_tm; tm',n_tm; ptm,p_tm; atm,a_tm]
                                pth_recodel in
                 let th4 = PROVE_HYP th1 th3 in
                 EQ_MP th4 (TRANS th2 (SYM(NUM_ADD_RULE atm tm')))
            | (_,Comb(Const("BIT1",_),Comb(Const("BIT1",_),_))) ->
                 let th1 = NUM_ADC_RULE zero_tm tm' in
                 let ptm = rand(concl th1) in
                 let th2 = NUM_MUL_RULE k l tm ptm in
                 let atm = subbn (rand(concl th2)) tm in
                 let th3 = INST [tm,m_tm; tm',n_tm; ptm,p_tm; atm,a_tm]
                                pth_recoder in
                 let th4 = PROVE_HYP th1 th3 in
                 EQ_MP th4 (TRANS th2 (SYM(NUM_ADD_RULE atm tm)))
            | _ ->
                 if k <= l then
                   let th0 = NUM_MUL_RULE (k - 1) l mtm tm' in
                   let ptm = rand(concl th0) in
                   let th1 =
                    EQ_MP (INST [mtm,m_tm; tm',n_tm; ptm,p_tm] pth_oddl) th0 in
                   let tm1 = lhand(rand(concl th1)) in
                   TRANS th1 (NUM_ADD_RULE tm1 tm')
                 else
                   let th0 = NUM_MUL_RULE k (l - 1) tm ntm in
                   let ptm = rand(concl th0) in
                   let th1 =
                     EQ_MP (INST [tm,m_tm; ntm,n_tm; ptm,p_tm] pth_oddr) th0 in
                   let tm1 = lhand(rand(concl th1)) in
                   TRANS th1 (NUM_ADD_RULE tm1 tm)
          else
             let mval = dest_raw_numeral mtm
             and nval = dest_raw_numeral ntm in
             if nval <=/ mval then
               let ptm = rand(mk_numeral(mval -/ nval)) in
               let th2 = NUM_ADD_RULE ntm ptm
               and th3 = NUM_ADC_RULE mtm ntm in
               let atm = rand(concl th3) in
               let th4 = NUM_SQUARE_RULE ptm in
               let btm = rand(concl th4) in
               let th5 = NUM_SQUARE_RULE atm in
               let ctm = rand(concl th5) in
               let dtm = subbn ctm btm in
               let th6 = NUM_ADD_RULE btm dtm in
               let th1 = INST [atm,a_tm; btm,b_tm; ctm,c_tm; dtm,d_tm;
                               mtm,m_tm; ntm,n_tm; ptm,p_tm] pth_oo1 in
               QUICK_PROVE_HYP  (end_itlist CONJ
                   [th2;th3;th4;th5;th6]) th1
             else
               let ptm = rand(mk_numeral(nval -/ mval)) in
               let th2 = NUM_ADD_RULE mtm ptm
               and th3 = NUM_ADC_RULE ntm mtm in
               let atm = rand(concl th3) in
               let th4 = NUM_SQUARE_RULE ptm in
               let btm = rand(concl th4) in
               let th5 = NUM_SQUARE_RULE atm in
               let ctm = rand(concl th5) in
               let dtm = subbn ctm btm in
               let th6 = NUM_ADD_RULE btm dtm in
               let th1 = INST [atm,a_tm; btm,b_tm; ctm,c_tm; dtm,d_tm;
                               mtm,m_tm; ntm,n_tm; ptm,p_tm] pth_oo2 in
               QUICK_PROVE_HYP  (end_itlist CONJ
                   [th2;th3;th4;th5;th6]) th1
      | _ -> failwith "NUM_MUL_RULE" in
    NUM_MUL_RULE in
  let NUM_MULT_CONV' =
    let pth_refl = (STANDARDIZE o MESON[EXP_2])
      `m EXP 2 = p <=> m * m = p` in
    fun tm ->
      match tm with
        Comb(Comb(Const("*",_),mtm),ntm) ->
            if compare mtm ntm = 0 then
              let th1 = NUM_SQUARE_RULE mtm in
              let ptm = rand(concl th1) in
              EQ_MP (INST [mtm,m_tm;ptm,p_tm] pth_refl) th1
            else
              let w1,z1 = bitcounts mtm and w2,z2 = bitcounts ntm in
              NUM_MUL_RULE (w1+z1) (w2+z2) mtm ntm
    | _ -> failwith "NUM_MULT_CONV'" in
  let NUM_SUC_CONV =
    let pth = (STANDARDIZE o prove)
     (`SUC(_0 + m) = n <=> SUC(NUMERAL m) = NUMERAL n`,
      BINOP_TAC THEN MESON_TAC[NUMERAL; ADD_CLAUSES]) in
    fun tm ->
      match tm with
        Comb(Const("SUC",_),Comb(Const("NUMERAL",_),mtm))
        when wellformed mtm ->
          let th1 = NUM_ADC_RULE zero_tm mtm in
          let ntm = rand(concl th1) in
          EQ_MP(INST [mtm,m_tm; ntm,n_tm] pth) th1
      | _ -> failwith "NUM_SUC_CONV" in
  let NUM_ADD_CONV =
    let topthm_add = (STANDARDIZE o MESON[NUMERAL])
      `m + n = p <=> NUMERAL m + NUMERAL n = NUMERAL p` in
    fun tm ->
      match tm with
        Comb(Comb(Const("+",_),Comb(Const("NUMERAL",_),mtm)),
          Comb(Const("NUMERAL",_),ntm))
        when wellformed mtm && wellformed ntm ->
        let th1 = NUM_ADD_RULE mtm ntm in
        let ptm = rand(concl th1) in
        let th2 = INST [mtm,m_tm; ntm,n_tm; ptm,p_tm] topthm_add in
        EQ_MP th2 th1
      | _ -> failwith "NUM_ADD_CONV" in
  let NUM_MULT_CONV =
    let topthm_mul = (STANDARDIZE o MESON[NUMERAL])
      `m * n = p <=> NUMERAL m * NUMERAL n = NUMERAL p`
    and pth_refl = (STANDARDIZE o MESON[NUMERAL; EXP_2])
      `m EXP 2 = p <=> NUMERAL m * NUMERAL m = NUMERAL p` in
    fun tm ->
      match tm with
        Comb(Comb(Const("*",_),Comb(Const("NUMERAL",_),mtm)),
          Comb(Const("NUMERAL",_),ntm)) ->
            if compare mtm ntm = 0 then
              let th1 = NUM_SQUARE_RULE mtm in
              let ptm = rand(concl th1) in
              EQ_MP (INST [mtm,m_tm;ptm,p_tm] pth_refl) th1
            else
              let w1,z1 = bitcounts mtm and w2,z2 = bitcounts ntm in
              let th1 = NUM_MUL_RULE (w1+z1) (w2+z2) mtm ntm in
              let ptm = rand(concl th1) in
              let th2 = INST [mtm,m_tm; ntm,n_tm; ptm,p_tm] topthm_mul in
              EQ_MP th2 th1
      | _ -> failwith "NUM_MULT_CONV" in
  let NUM_EXP_CONV =
    let pth0 = (STANDARDIZE o prove)
     (`(m EXP n = p) ==> (p * p = a) ==> (m EXP (BIT0 n) = a)`,
       REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
       REWRITE_TAC[BIT0; EXP_ADD])
    and pth1 = (STANDARDIZE o prove)
     (`(m EXP n = p) ==> (p * p = b) ==> (m * b = a) ==> (m EXP (BIT1 n) = a)`,
      REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
      REWRITE_TAC[BIT1; EXP_ADD; EXP])
    and pth = (STANDARDIZE o prove)
     (`m EXP _0 = BIT1 _0`,
      MP_TAC (CONJUNCT1 EXP) THEN REWRITE_TAC[NUMERAL; BIT1] THEN
      DISCH_THEN MATCH_ACCEPT_TAC)
    and tth = (STANDARDIZE o prove)
     (`(NUMERAL m) EXP (NUMERAL n) = m EXP n`,
      REWRITE_TAC[NUMERAL])
    and fth = (STANDARDIZE o prove)
     (`m = NUMERAL m`,
      REWRITE_TAC[NUMERAL]) in
    let tconv = GEN_REWRITE_CONV I [tth] in
    let rec NUM_EXP_CONV l r =
      if r = zero_tm then INST [l,m_tm] pth else
      let b,r' = dest_comb r in
      if b = BIT0_tm then
        let th1 = NUM_EXP_CONV l r' in
        let tm1 = rand(concl th1) in
        let th2 = NUM_MULT_CONV' (mk_binop mul_tm tm1 tm1) in
        let tm2 = rand(concl th2) in
        MP (MP (INST [l,m_tm; r',n_tm; tm1,p_tm; tm2,a_tm] pth0) th1) th2
      else
        let th1 = NUM_EXP_CONV l r' in
        let tm1 = rand(concl th1) in
        let th2 = NUM_MULT_CONV' (mk_binop mul_tm tm1 tm1) in
        let tm2 = rand(concl th2) in
        let th3 = NUM_MULT_CONV' (mk_binop mul_tm l tm2) in
        let tm3 = rand(concl th3) in
        MP (MP (MP (INST [l,m_tm; r',n_tm; tm1,p_tm; tm2,b_tm; tm3,a_tm]
                         pth1) th1) th2) th3 in
    fun tm -> try let th = tconv tm in
                  let lop,r = dest_comb (rand(concl th)) in
                  let _,l = dest_comb lop in
                  if not (wellformed l && wellformed r) then failwith "" else
                  let th' = NUM_EXP_CONV l r in
                  let tm' = rand(concl th') in
                  TRANS (TRANS th th') (INST [tm',m_tm] fth)
              with Failure _ -> failwith "NUM_EXP_CONV" in
  let NUM_LT_CONV =
    let pth = (UNDISCH o STANDARDIZE o prove)
     (`SUC(m + n) = p ==> ((NUMERAL n < NUMERAL p) <=> T)`,
      REWRITE_TAC[NUMERAL; LT_EXISTS; ADD_CLAUSES] THEN
      MESON_TAC[ADD_SYM])
    and qth = (UNDISCH o STANDARDIZE o prove)
     (`m + p = n ==> (NUMERAL n < NUMERAL p <=> F)`,
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[NOT_LT; NUMERAL] THEN
      MESON_TAC[LE_ADD; ADD_SYM])
    and rth = (STANDARDIZE o prove)
     (`NUMERAL n < NUMERAL n <=> F`,
      MESON_TAC[LT_REFL]) in
    fun tm ->
      match tm with
        Comb(Comb(Const("<",_),Comb(Const("NUMERAL",_),mtm)),
             Comb(Const("NUMERAL",_),ntm)) ->
          let rel = orderrelation mtm ntm in
          if rel = 0 then INST[ntm,n_tm] rth
          else if rel < 0 then
            let dtm = sbcbn ntm mtm in
            let th = NUM_ADC_RULE dtm mtm in
            QUICK_PROVE_HYP th (INST [dtm,m_tm; mtm,n_tm; ntm,p_tm] pth)
          else
            let dtm = subbn mtm ntm in
            let th = NUM_ADD_RULE dtm ntm in
            QUICK_PROVE_HYP th (INST [dtm,m_tm; mtm,n_tm; ntm,p_tm] qth)
      | _ -> failwith "NUM_LT_CONV"
  and NUM_LE_CONV =
    let pth = (UNDISCH o STANDARDIZE o prove)
     (`m + n = p ==> ((NUMERAL n <= NUMERAL p) <=> T)`,
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[NUMERAL] THEN
      MESON_TAC[LE_ADD; ADD_SYM])
    and qth = (UNDISCH o STANDARDIZE o prove)
     (`SUC(m + p) = n ==> (NUMERAL n <= NUMERAL p <=> F)`,
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[NUMERAL; NOT_LE; ADD_CLAUSES; LT_EXISTS] THEN
      MESON_TAC[ADD_SYM])
    and rth = (STANDARDIZE o prove)
     (`NUMERAL n <= NUMERAL n <=> T`,
      REWRITE_TAC[LE_REFL]) in
    fun tm ->
      match tm with
        Comb(Comb(Const("<=",_),Comb(Const("NUMERAL",_),mtm)),
             Comb(Const("NUMERAL",_),ntm)) ->
          let rel = orderrelation mtm ntm in
          if rel = 0 then INST[ntm,n_tm] rth
          else if rel < 0 then
            let dtm = subbn ntm mtm in
            let th = NUM_ADD_RULE dtm mtm in
            QUICK_PROVE_HYP th (INST [dtm,m_tm; mtm,n_tm; ntm,p_tm] pth)
          else
            let dtm = sbcbn mtm ntm in
            let th = NUM_ADC_RULE dtm ntm in
            QUICK_PROVE_HYP th (INST [dtm,m_tm; mtm,n_tm; ntm,p_tm] qth)
      | _ -> failwith "NUM_LE_CONV"
  and NUM_EQ_CONV =
    let pth = (UNDISCH o STANDARDIZE o prove)
     (`SUC(m + n) = p ==> ((NUMERAL n = NUMERAL p) <=> F)`,
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[NUMERAL; GSYM LE_ANTISYM; DE_MORGAN_THM] THEN
      REWRITE_TAC[NOT_LE; LT_EXISTS; ADD_CLAUSES] THEN
      MESON_TAC[ADD_SYM])
    and qth = (UNDISCH o STANDARDIZE o prove)
     (`SUC(m + p) = n ==> ((NUMERAL n = NUMERAL p) <=> F)`,
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[NUMERAL; GSYM LE_ANTISYM; DE_MORGAN_THM] THEN
      REWRITE_TAC[NOT_LE; LT_EXISTS; ADD_CLAUSES] THEN
      MESON_TAC[ADD_SYM])
    and rth = (STANDARDIZE o prove)
     (`(NUMERAL n = NUMERAL n) <=> T`,
      REWRITE_TAC[]) in
    fun tm ->
      match tm with
        Comb(Comb(Const("=",_),Comb(Const("NUMERAL",_),mtm)),
             Comb(Const("NUMERAL",_),ntm)) ->
          let rel = orderrelation mtm ntm in
          if rel = 0 then INST [ntm,n_tm] rth
          else if rel < 0 then
             let dtm = sbcbn ntm mtm in
             let th = NUM_ADC_RULE dtm mtm in
             QUICK_PROVE_HYP th (INST [dtm,m_tm; mtm,n_tm; ntm,p_tm] pth)
          else
             let dtm = sbcbn mtm ntm in
             let th = NUM_ADC_RULE dtm ntm in
             QUICK_PROVE_HYP th (INST [dtm,m_tm; mtm,n_tm; ntm,p_tm] qth)
      | _ -> failwith "NUM_EQ_CONV" in
  NUM_SUC_CONV,NUM_ADD_CONV,NUM_MULT_CONV,NUM_EXP_CONV,
  NUM_LT_CONV,NUM_LE_CONV,NUM_EQ_CONV;;

let NUM_GT_CONV = GEN_REWRITE_CONV I [GT] THENC NUM_LT_CONV;;

let NUM_GE_CONV = GEN_REWRITE_CONV I [GE] THENC NUM_LE_CONV;;

let NUM_PRE_CONV =
  let tth = prove
   (`PRE 0 = 0`,
    REWRITE_TAC[PRE]) in
  let pth = prove
   (`(SUC m = n) ==> (PRE n = m)`,
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[PRE])
  and m = `m:num` and n = `n:num` in
  let suc = `SUC` in
  let pre = `PRE` in
  fun tm -> try let l,r = dest_comb tm in
                if not (l = pre) then fail() else
                let x = dest_numeral r in
                if x =/ num 0 then tth else
                let tm' = mk_numeral (x -/ num 1) in
                let th1 = NUM_SUC_CONV (mk_comb(suc,tm')) in
                MP (INST [tm',m; r,n] pth) th1
            with Failure _ -> failwith "NUM_PRE_CONV";;

let NUM_SUB_CONV =
  let pth0 = prove
   (`p <= n ==> (p - n = 0)`,
    REWRITE_TAC[SUB_EQ_0])
  and pth1 = prove
   (`(m + n = p) ==> (p - n = m)`,
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[ADD_SUB])
  and m = `m:num` and n = `n:num` and p = `p:num`
  and minus = `(-)`
  and plus = `(+)`
  and le = `(<=)` in
  fun tm -> try let l,r = dest_binop minus tm in
                let ln = dest_numeral l
                and rn = dest_numeral r in
                if  ln <=/ rn then
                  let pth = INST [l,p; r,n] pth0
                  and th0 = EQT_ELIM(NUM_LE_CONV (mk_binop le l r)) in
                  MP pth th0
                else
                  let kn = ln -/ rn in
                  let k = mk_numeral kn in
                  let pth = INST [k,m; l,p; r,n] pth1
                  and th0 = NUM_ADD_CONV (mk_binop plus k r) in
                  MP pth th0
            with Failure _ -> failwith "NUM_SUB_CONV";;

let NUM_DIV_CONV,NUM_MOD_CONV =
  let pth = prove
   (`q * n + r = m ==> r < n ==> m DIV n = q /\ m MOD n = r`,
    MESON_TAC[DIVMOD_UNIQ])
  and pth0 = prove
   (`!m. m DIV 0 = 0 /\ m MOD 0 = m`,
    REWRITE_TAC[DIV_ZERO; MOD_ZERO])
  and m = `m:num` and n = `n:num` and q = `q:num` and r = `r:num`
  and dtm = `(DIV)` and mtm = `(MOD)` in
  let NUM_DIVMOD_CONV x y =
    if y =/ num_0 then SPEC (mk_numeral x) pth0 else
    let k = quo_num x y
    and l = mod_num x y in
    let th0 = INST [mk_numeral x,m; mk_numeral y,n;
                    mk_numeral k,q; mk_numeral l,r] pth in
    let tm0 = lhand(lhand(concl th0)) in
    let th1 = (LAND_CONV NUM_MULT_CONV THENC NUM_ADD_CONV) tm0 in
    let th2 = MP th0 th1 in
    let tm2 = lhand(concl th2) in
    MP th2 (EQT_ELIM(NUM_LT_CONV tm2)) in
  (fun tm -> try let xt,yt = dest_binop dtm tm in
                 CONJUNCT1(NUM_DIVMOD_CONV (dest_numeral xt) (dest_numeral yt))
             with Failure _ -> failwith "NUM_DIV_CONV"),
  (fun tm -> try let xt,yt = dest_binop mtm tm in
                 CONJUNCT2(NUM_DIVMOD_CONV (dest_numeral xt) (dest_numeral yt))
             with Failure _ -> failwith "NUM_MOD_CONV");;

let NUM_FACT_CONV =
  let suc = `SUC`
  and mul = `(*)` in
  let pth_0 = prove
   (`FACT 0 = 1`,
    REWRITE_TAC[FACT])
  and pth_suc = prove
   (`(SUC x = y) ==> (FACT x = w) ==> (y * w = z) ==> (FACT y = z)`,
    REPEAT (DISCH_THEN(SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[FACT])
  and w = `w:num` and x = `x:num` and y = `y:num` and z = `z:num` in
  let mksuc n =
    let n' = n -/ (num 1) in
    NUM_SUC_CONV (mk_comb(suc,mk_numeral n')) in
  let rec NUM_FACT_CONV n =
    if n =/ num 0 then pth_0 else
    let th0 = mksuc n in
    let tmx = rand(lhand(concl th0)) in
    let tm0 = rand(concl th0) in
    let th1 = NUM_FACT_CONV (n -/ num 1) in
    let tm1 = rand(concl th1) in
    let th2 = NUM_MULT_CONV (mk_binop mul tm0 tm1) in
    let tm2 = rand(concl th2) in
    let pth = INST [tmx,x; tm0, y; tm1,w; tm2,z] pth_suc in
    MP (MP (MP pth th0) th1) th2 in
  fun tm ->
    try let l,r = dest_comb tm in
        if fst(dest_const l) = "FACT"
        then NUM_FACT_CONV (dest_numeral r)
        else fail()
    with Failure _ -> failwith "NUM_FACT_CONV";;

let NUM_MAX_CONV =
  REWR_CONV MAX THENC
  RATOR_CONV(RATOR_CONV(RAND_CONV NUM_LE_CONV)) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES];;

let NUM_MIN_CONV =
  REWR_CONV MIN THENC
  RATOR_CONV(RATOR_CONV(RAND_CONV NUM_LE_CONV)) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES];;

(* ------------------------------------------------------------------------- *)
(* Final hack-together.                                                      *)
(* ------------------------------------------------------------------------- *)

let NUM_REL_CONV =
  let gconv_net = itlist (uncurry net_of_conv)
    [`NUMERAL m < NUMERAL n`,NUM_LT_CONV;
     `NUMERAL m <= NUMERAL n`,NUM_LE_CONV;
     `NUMERAL m > NUMERAL n`,NUM_GT_CONV;
     `NUMERAL m >= NUMERAL n`,NUM_GE_CONV;
     `NUMERAL m = NUMERAL n`,NUM_EQ_CONV]
    (basic_net()) in
  REWRITES_CONV gconv_net;;

let num_red_conv_list =
  [`SUC(NUMERAL n)`,NUM_SUC_CONV;
   `PRE(NUMERAL n)`,NUM_PRE_CONV;
   `FACT(NUMERAL n)`,NUM_FACT_CONV;
   `NUMERAL m < NUMERAL n`,NUM_LT_CONV;
   `NUMERAL m <= NUMERAL n`,NUM_LE_CONV;
   `NUMERAL m > NUMERAL n`,NUM_GT_CONV;
   `NUMERAL m >= NUMERAL n`,NUM_GE_CONV;
   `NUMERAL m = NUMERAL n`,NUM_EQ_CONV;
   `EVEN(NUMERAL n)`,NUM_EVEN_CONV;
   `ODD(NUMERAL n)`,NUM_ODD_CONV;
   `NUMERAL m + NUMERAL n`,NUM_ADD_CONV;
   `NUMERAL m - NUMERAL n`,NUM_SUB_CONV;
   `NUMERAL m * NUMERAL n`,NUM_MULT_CONV;
   `(NUMERAL m) EXP (NUMERAL n)`,NUM_EXP_CONV;
   `(NUMERAL m) DIV (NUMERAL n)`,NUM_DIV_CONV;
   `(NUMERAL m) MOD (NUMERAL n)`,NUM_MOD_CONV;
   `MAX (NUMERAL m) (NUMERAL n)`,NUM_MAX_CONV;
   `MIN (NUMERAL m) (NUMERAL n)`,NUM_MIN_CONV];;

let NUM_RED_CONV =
  let gconv_net = itlist (uncurry net_of_conv) num_red_conv_list
    (basic_net()) in
  REWRITES_CONV gconv_net;;

let NUM_REDUCE_CONV = DEPTH_CONV NUM_RED_CONV;;

let num_compute_add_convs =
  let convlist = map (fun pat,the_conv ->
    let c,args = strip_comb pat in (c,length args,the_conv))
    num_red_conv_list in
  fun (compset:Compute.compset) ->
    itlist (fun newc () -> Compute.add_conv newc compset) convlist ();;

let NUM_COMPUTE_CONV =
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  num_compute_add_convs cs;
  Compute.WEAK_CBV_CONV cs;;

let NUM_REDUCE_TAC = CONV_TAC NUM_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* I do like this after all...                                               *)
(* ------------------------------------------------------------------------- *)

let num_CONV =
  let SUC_tm = `SUC` in
  fun tm ->
    let n = dest_numeral tm -/ num 1 in
    if n </ num 0 then failwith "num_CONV" else
    let tm' = mk_numeral n in
    SYM(NUM_SUC_CONV (mk_comb(SUC_tm,tm')));;

(* ------------------------------------------------------------------------- *)
(* Expands "!n. n < numeral-constant ==> P(n)" into all the cases.           *)
(* ------------------------------------------------------------------------- *)

let EXPAND_CASES_CONV =
  let pth_base = prove
   (`(!n. n < 0 ==> P n) <=> T`,
    REWRITE_TAC[LT])
  and pth_step = prove
   (`(!n. n < SUC k ==> P n) <=> (!n. n < k ==> P n) /\ P k`,
    REWRITE_TAC[LT] THEN MESON_TAC[]) in
  let base_CONV = GEN_REWRITE_CONV I [pth_base]
  and step_CONV =
    BINDER_CONV(LAND_CONV(RAND_CONV num_CONV)) THENC
    GEN_REWRITE_CONV I [pth_step] in
  let rec conv tm =
    (base_CONV ORELSEC (step_CONV THENC LAND_CONV conv)) tm in
  conv THENC (REWRITE_CONV[GSYM CONJ_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Computation of (a EXP k) MOD n keeping intermediates reduced              *)
(* ------------------------------------------------------------------------- *)

let EXP_MOD_CONV =
  let [pth_0; pth_even; pth_odd] = (CONJUNCTS o prove)
   (`(a EXP 0) MOD n = 1 MOD n /\
     (a EXP (NUMERAL(BIT0 k))) MOD n =
     ((a EXP (NUMERAL k) MOD n) EXP 2) MOD n /\
     (a EXP (NUMERAL(BIT1 k))) MOD n =
     (a * ((a EXP (NUMERAL k) MOD n) EXP 2) MOD n) MOD n`,
    REWRITE_TAC[EXP; EXP_2] THEN REWRITE_TAC[BIT0; BIT1; NUMERAL] THEN
    REWRITE_TAC[EXP; EXP_ADD] THEN CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[]) in
  let conv_zero = GEN_REWRITE_CONV I [MOD_ZERO]
  and conv_0 = GEN_REWRITE_CONV I [pth_0]
  and conv_even = GEN_REWRITE_CONV I [pth_even]
  and conv_odd = GEN_REWRITE_CONV I [pth_odd] in
  let rec conv tm =
    ((conv_0 THENC NUM_MOD_CONV) ORELSEC
     (conv_even THENC
      LAND_CONV(LAND_CONV conv THENC NUM_EXP_CONV) THENC
      NUM_MOD_CONV) ORELSEC
     (conv_odd THENC
      LAND_CONV(RAND_CONV(LAND_CONV(LAND_CONV conv THENC NUM_EXP_CONV) THENC
                          NUM_MOD_CONV) THENC
                NUM_MULT_CONV) THENC
      NUM_MOD_CONV)) tm in
  let fullconv = (conv_zero THENC NUM_EXP_CONV) ORELSEC conv in
  fun tm ->
    match tm with
      Comb(Comb(Const("MOD",_),
                Comb(Comb(Const("EXP",_),m),k)),n)
      when is_numeral m && is_numeral k && is_numeral n -> fullconv tm
  | _ -> failwith "EXP_MOD_CONV";;
