(* ========================================================================= *)
(* Framework for universal real decision procedures, and a simple instance.  *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "calc_int.ml";;

(* ------------------------------------------------------------------------- *)
(* Some lemmas needed now just to drive the decision procedure.              *)
(* ------------------------------------------------------------------------- *)

let REAL_LTE_TOTAL = prove
 (`!x y. x < y \/ y <= x`,
  REWRITE_TAC[real_lt] THEN CONV_TAC TAUT);;

let REAL_LET_TOTAL = prove
 (`!x y. x <= y \/ y < x`,
  REWRITE_TAC[real_lt] THEN CONV_TAC TAUT);;

let REAL_LT_IMP_LE = prove
 (`!x y. x < y ==> x <= y`,
  MESON_TAC[real_lt; REAL_LE_TOTAL]);;

let REAL_LTE_TRANS = prove
 (`!x y z. x < y /\ y <= z ==> x < z`,
  MESON_TAC[real_lt; REAL_LE_TRANS]);;

let REAL_LET_TRANS = prove
 (`!x y z. x <= y /\ y < z ==> x < z`,
  MESON_TAC[real_lt; REAL_LE_TRANS]);;

let REAL_LT_TRANS = prove
 (`!x y z. x < y /\ y < z ==> x < z`,
  MESON_TAC[REAL_LTE_TRANS; REAL_LT_IMP_LE]);;

let REAL_LE_ADD = prove
 (`!x y. &0 <= x /\ &0 <= y ==> &0 <= x + y`,
  MESON_TAC[REAL_LE_LADD_IMP; REAL_ADD_RID; REAL_LE_TRANS]);;

let REAL_LTE_ANTISYM = prove
 (`!x y. ~(x < y /\ y <= x)`,
  MESON_TAC[real_lt]);;

let REAL_SUB_LE = prove
 (`!x y. &0 <= (x - y) <=> y <= x`,
  REWRITE_TAC[real_sub; GSYM REAL_LE_LNEG; REAL_LE_NEG2]);;

let REAL_NEG_SUB = prove
 (`!x y. --(x - y) = y - x`,
  REWRITE_TAC[real_sub; REAL_NEG_ADD; REAL_NEG_NEG] THEN
  REWRITE_TAC[REAL_ADD_AC]);;

let REAL_LE_LT = prove
 (`!x y. x <= y <=> x < y \/ (x = y)`,
  REWRITE_TAC[real_lt] THEN MESON_TAC[REAL_LE_ANTISYM; REAL_LE_TOTAL]);;

let REAL_SUB_LT = prove
 (`!x y. &0 < (x - y) <=> y < x`,
  REWRITE_TAC[real_lt] THEN ONCE_REWRITE_TAC[GSYM REAL_NEG_SUB] THEN
  REWRITE_TAC[REAL_LE_LNEG; REAL_ADD_RID; REAL_SUB_LE]);;

let REAL_NOT_LT = prove
 (`!x y. ~(x < y) <=> y <= x`,
  REWRITE_TAC[real_lt]);;

let REAL_SUB_0 = prove
 (`!x y. (x - y = &0) <=> (x = y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM REAL_NOT_LT] THEN
  REWRITE_TAC[REAL_SUB_LE; REAL_SUB_LT] THEN REWRITE_TAC[REAL_NOT_LT]);;

let REAL_LT_LE = prove
 (`!x y. x < y <=> x <= y /\ ~(x = y)`,
  MESON_TAC[real_lt; REAL_LE_TOTAL; REAL_LE_ANTISYM]);;

let REAL_LT_REFL = prove
 (`!x. ~(x < x)`,
  REWRITE_TAC[real_lt; REAL_LE_REFL]);;

let REAL_LTE_ADD = prove
 (`!x y. &0 < x /\ &0 <= y ==> &0 < x + y`,
  MESON_TAC[REAL_LE_LADD_IMP; REAL_ADD_RID; REAL_LTE_TRANS]);;

let REAL_LET_ADD = prove
 (`!x y. &0 <= x /\ &0 < y ==> &0 < x + y`,
  MESON_TAC[REAL_LTE_ADD; REAL_ADD_SYM]);;

let REAL_LT_ADD = prove
 (`!x y. &0 < x /\ &0 < y ==> &0 < x + y`,
  MESON_TAC[REAL_LT_IMP_LE; REAL_LTE_ADD]);;

let REAL_ENTIRE = prove
 (`!x y. (x * y = &0) <=> (x = &0) \/ (y = &0)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `(*) (inv x)`) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RZERO]);;

let REAL_LE_NEGTOTAL = prove
 (`!x. &0 <= x \/ &0 <= --x`,
  REWRITE_TAC[REAL_LE_RNEG; REAL_ADD_LID; REAL_LE_TOTAL]);;

let REAL_LE_SQUARE = prove
 (`!x. &0 <= x * x`,
  GEN_TAC THEN DISJ_CASES_TAC(SPEC `x:real` REAL_LE_NEGTOTAL) THEN
  POP_ASSUM(fun th -> MP_TAC(MATCH_MP REAL_LE_MUL (CONJ th th))) THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG]);;

let REAL_MUL_RID = prove
 (`!x. x * &1 = x`,
  MESON_TAC[REAL_MUL_LID; REAL_MUL_SYM]);;

let REAL_POW_2 = prove
 (`!x. x pow 2 = x * x`,
  REWRITE_TAC[num_CONV `2`; num_CONV `1`] THEN
  REWRITE_TAC[real_pow; REAL_MUL_RID]);;

let REAL_POLY_CLAUSES = prove
 (`(!x y z. x + (y + z) = (x + y) + z) /\
   (!x y. x + y = y + x) /\
   (!x. &0 + x = x) /\
   (!x y z. x * (y * z) = (x * y) * z) /\
   (!x y. x * y = y * x) /\
   (!x. &1 * x = x) /\
   (!x. &0 * x = &0) /\
   (!x y z. x * (y + z) = x * y + x * z) /\
   (!x. x pow 0 = &1) /\
   (!x n. x pow (SUC n) = x * x pow n)`,
  REWRITE_TAC[real_pow; REAL_ADD_LDISTRIB; REAL_MUL_LZERO] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; REAL_ADD_LID; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_ADD_AC] THEN REWRITE_TAC[REAL_MUL_SYM]);;

let REAL_POLY_NEG_CLAUSES = prove
 (`(!x. --x = --(&1) * x) /\
   (!x y. x - y = x + --(&1) * y)`,
  REWRITE_TAC[REAL_MUL_LNEG; real_sub; REAL_MUL_LID]);;

let REAL_POS = prove
 (`!n. &0 <= &n`,
  REWRITE_TAC[REAL_OF_NUM_LE; LE_0]);;

let REAL_LT_NZ = prove
 (`!n. ~(&n = &0) <=> (&0 < &n)`,
  GEN_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
  CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  ASM_CASES_TAC `&n = &0` THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_POS]);;

let REAL_POS_LT = prove
 (`!n. &0 < &(SUC n)`,
  GEN_TAC THEN REWRITE_TAC [SPEC `SUC n` (GSYM REAL_LT_NZ);
                            REAL_OF_NUM_EQ] THEN
  REWRITE_TAC[GSYM LT_NZ; LT_0]);;

(* ------------------------------------------------------------------------- *)
(* Data structure for Positivstellensatz refutations.                        *)
(* ------------------------------------------------------------------------- *)

type positivstellensatz =
   Axiom_eq of int
 | Axiom_le of int
 | Axiom_lt of int
 | Rational_eq of num
 | Rational_le of num
 | Rational_lt of num
 | Square of term
 | Eqmul of term * positivstellensatz
 | Sum of positivstellensatz * positivstellensatz
 | Product of positivstellensatz * positivstellensatz;;

(* ------------------------------------------------------------------------- *)
(* Parametrized reals decision procedure.                                    *)
(*                                                                           *)
(* This is a bootstrapping version, and subsequently gets overwritten twice  *)
(* with more specialized versions, once here and finally in "calc_rat.ml".   *)
(* ------------------------------------------------------------------------- *)

let GEN_REAL_ARITH =
  let pth = prove
   (`(x < y <=> y - x > &0) /\
     (x <= y <=> y - x >= &0) /\
     (x > y <=> x - y > &0) /\
     (x >= y <=> x - y >= &0) /\
     ((x = y) <=> (x - y = &0)) /\
     (~(x < y) <=> x - y >= &0) /\
     (~(x <= y) <=> x - y > &0) /\
     (~(x > y) <=> y - x >= &0) /\
     (~(x >= y) <=> y - x > &0) /\
     (~(x = y) <=> x - y > &0 \/ --(x - y) > &0)`,
    REWRITE_TAC[real_gt; real_ge; REAL_SUB_LT; REAL_SUB_LE; REAL_NEG_SUB] THEN
    REWRITE_TAC[REAL_SUB_0; real_lt] THEN MESON_TAC[REAL_LE_ANTISYM])
  and pth_final = TAUT `(~p ==> F) ==> p`
  and pth_add = prove
   (`((x = &0) /\ (y = &0) ==> (x + y = &0)) /\
     ((x = &0) /\ y >= &0 ==> x + y >= &0) /\
     ((x = &0) /\ y > &0 ==> x + y > &0) /\
     (x >= &0 /\ (y = &0) ==> x + y >= &0) /\
     (x >= &0 /\ y >= &0 ==> x + y >= &0) /\
     (x >= &0 /\ y > &0 ==> x + y > &0) /\
     (x > &0 /\ (y = &0) ==> x + y > &0) /\
     (x > &0 /\ y >= &0 ==> x + y > &0) /\
     (x > &0 /\ y > &0 ==> x + y > &0)`,
    SIMP_TAC[REAL_ADD_LID; REAL_ADD_RID; real_ge; real_gt] THEN
    REWRITE_TAC[REAL_LE_LT] THEN
    MESON_TAC[REAL_ADD_LID; REAL_ADD_RID; REAL_LT_ADD])
  and pth_mul = prove
   (`((x = &0) /\ (y = &0) ==> (x * y = &0)) /\
     ((x = &0) /\ y >= &0 ==> (x * y = &0)) /\
     ((x = &0) /\ y > &0 ==> (x * y = &0)) /\
     (x >= &0 /\ (y = &0) ==> (x * y = &0)) /\
     (x >= &0 /\ y >= &0 ==> x * y >= &0) /\
     (x >= &0 /\ y > &0 ==> x * y >= &0) /\
     (x > &0 /\ (y = &0) ==> (x * y = &0)) /\
     (x > &0 /\ y >= &0 ==> x * y >= &0) /\
     (x > &0 /\ y > &0 ==> x * y > &0)`,
    SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; real_ge; real_gt] THEN
    SIMP_TAC[REAL_LT_LE; REAL_LE_MUL] THEN MESON_TAC[REAL_ENTIRE])
  and pth_emul = prove
   (`(y = &0) ==> !x. x * y = &0`,
    SIMP_TAC[REAL_MUL_RZERO])
  and pth_square = prove
   (`!x. x * x >= &0`,
    REWRITE_TAC[real_ge; REAL_POW_2; REAL_LE_SQUARE])
  and MATCH_MP_RULE th =
    let net = itlist
     (fun th -> net_of_conv (lhand(concl th)) (PART_MATCH lhand th))
     (CONJUNCTS th) empty_net in
    fun th -> MP (REWRITES_CONV net (concl th)) th
  and x_tm = `x:real` and y_tm = `y:real`
  and neg_tm = `(--):real->real`
  and gt_tm = `(>):real->real->bool`
  and ge_tm = `(>=):real->real->bool`
  and eq_tm = `(=):real->real->bool`
  and p_tm = `p:bool`
  and or_tm = `(\/)`
  and false_tm = `F`
  and z_tm = `&0 :real`
  and xy_lt = `(x:real) < y`
  and xy_nlt = `~((x:real) < y)`
  and xy_le = `(x:real) <= y`
  and xy_nle = `~((x:real) <= y)`
  and xy_gt = `(x:real) > y`
  and xy_ngt = `~((x:real) > y)`
  and xy_ge = `(x:real) >= y`
  and xy_nge = `~((x:real) >= y)`
  and xy_eq = `x:real = y`
  and xy_ne = `~(x:real = y)` in
  let is_ge = is_binop ge_tm
  and is_gt = is_binop gt_tm
  and is_req = is_binop eq_tm in
  fun (mk_numeric,
       NUMERIC_EQ_CONV,NUMERIC_GE_CONV,NUMERIC_GT_CONV,
       POLY_CONV,POLY_NEG_CONV,POLY_ADD_CONV,POLY_MUL_CONV,
       absconv1,absconv2,prover) ->
  let REAL_INEQ_CONV pth tm =
    let lop,r = dest_comb tm in
    let th = INST [rand lop,x_tm; r,y_tm] pth in
    TRANS th (LAND_CONV POLY_CONV (rand(concl th))) in
  let [REAL_LT_CONV; REAL_LE_CONV; REAL_GT_CONV; REAL_GE_CONV; REAL_EQ_CONV;
       REAL_NOT_LT_CONV; REAL_NOT_LE_CONV; REAL_NOT_GT_CONV;
       REAL_NOT_GE_CONV; _] =
       map REAL_INEQ_CONV (CONJUNCTS pth)
  and REAL_NOT_EQ_CONV =
     let pth = last(CONJUNCTS pth) in
     fun tm ->
      let l,r = dest_eq tm in
      let th = INST [l,x_tm; r,y_tm] pth in
      let th_p = POLY_CONV(lhand(lhand(rand(concl th)))) in
      let th_x = AP_TERM neg_tm th_p in
      let th_n = CONV_RULE (RAND_CONV POLY_NEG_CONV) th_x in
      let th' = MK_DISJ (AP_THM (AP_TERM gt_tm th_p) z_tm)
                        (AP_THM (AP_TERM gt_tm th_n) z_tm) in
      TRANS th th' in
  let net_single = itlist (uncurry net_of_conv)
   [xy_lt,REAL_LT_CONV;
    xy_nlt,(fun t -> REAL_NOT_LT_CONV(rand t));
    xy_le,REAL_LE_CONV;
    xy_nle,(fun t -> REAL_NOT_LE_CONV(rand t));
    xy_gt,REAL_GT_CONV;
    xy_ngt,(fun t -> REAL_NOT_GT_CONV(rand t));
    xy_ge,REAL_GE_CONV;
    xy_nge,(fun t -> REAL_NOT_GE_CONV(rand t));
    xy_eq,REAL_EQ_CONV;
    xy_ne,(fun t -> REAL_NOT_EQ_CONV(rand t))]
   empty_net
  and net_double = itlist (uncurry net_of_conv)
   [xy_lt,(fun t -> REAL_LT_CONV t,REAL_NOT_LT_CONV t);
    xy_le,(fun t -> REAL_LE_CONV t,REAL_NOT_LE_CONV t);
    xy_gt,(fun t -> REAL_GT_CONV t,REAL_NOT_GT_CONV t);
    xy_ge,(fun t -> REAL_GE_CONV t,REAL_NOT_GE_CONV t);
    xy_eq,(fun t -> REAL_EQ_CONV t,REAL_NOT_EQ_CONV t)]
   empty_net in
  let REAL_INEQ_NORM_CONV = REWRITES_CONV net_single
  and REAL_INEQ_NORM_DCONV = REWRITES_CONV net_double in
  let NNF_NORM_CONV =
    GEN_NNF_CONV false (REAL_INEQ_NORM_CONV,REAL_INEQ_NORM_DCONV) in
  let MUL_RULE =
    let rules = MATCH_MP_RULE pth_mul in
    fun th -> CONV_RULE(LAND_CONV POLY_MUL_CONV) (rules th)
  and ADD_RULE =
    let rules = MATCH_MP_RULE pth_add in
    fun th -> CONV_RULE(LAND_CONV POLY_ADD_CONV) (rules th)
  and EMUL_RULE =
    let rule = MATCH_MP pth_emul in
    fun tm th -> CONV_RULE (LAND_CONV POLY_MUL_CONV)
                           (SPEC tm (rule th))
  and SQUARE_RULE t =
    CONV_RULE (LAND_CONV POLY_MUL_CONV) (SPEC t pth_square) in
  let hol_of_positivstellensatz(eqs,les,lts) =
    let rec translate prf =
      match prf with
        Axiom_eq n -> el n eqs
      | Axiom_le n -> el n les
      | Axiom_lt n -> el n lts
      | Rational_eq x ->
          EQT_ELIM(NUMERIC_EQ_CONV(mk_comb(mk_comb(eq_tm,mk_numeric x),z_tm)))
      | Rational_le x ->
          EQT_ELIM(NUMERIC_GE_CONV(mk_comb(mk_comb(ge_tm,mk_numeric x),z_tm)))
      | Rational_lt x ->
          EQT_ELIM(NUMERIC_GT_CONV(mk_comb(mk_comb(gt_tm,mk_numeric x),z_tm)))
      | Square t -> SQUARE_RULE t
      | Eqmul(t,p) -> EMUL_RULE t (translate p)
      | Sum(p1,p2) -> ADD_RULE (CONJ (translate p1) (translate p2))
      | Product(p1,p2) -> MUL_RULE (CONJ (translate p1) (translate p2)) in
    fun prf ->
      CONV_RULE(FIRST_CONV[NUMERIC_GE_CONV; NUMERIC_GT_CONV; NUMERIC_EQ_CONV])
               (translate prf) in
  let init_conv =
    TOP_DEPTH_CONV BETA_CONV THENC
    PRESIMP_CONV THENC
    NNF_CONV THENC DEPTH_BINOP_CONV or_tm CONDS_ELIM_CONV THENC
    NNF_NORM_CONV THENC
    SKOLEM_CONV THENC
    PRENEX_CONV THENC
    WEAK_DNF_CONV in
  let rec overall dun ths =
    match ths with
      [] ->
        let eq,ne = partition (is_req o concl) dun in
        let le,nl = partition (is_ge o concl) ne in
        let lt = filter (is_gt o concl) nl in
        prover hol_of_positivstellensatz (eq,le,lt)
    | th::oths ->
        let tm = concl th in
        if is_conj tm then
          let th1,th2 = CONJ_PAIR th in
          overall dun (th1::th2::oths)
        else if is_disj tm then
          let th1 = overall dun (ASSUME (lhand tm)::oths)
          and th2 = overall dun (ASSUME (rand tm)::oths) in
          DISJ_CASES th th1 th2
        else overall (th::dun) oths in
  fun tm ->
    let NNF_NORM_CONV' =
      GEN_NNF_CONV false
        (CACHE_CONV REAL_INEQ_NORM_CONV,fun t -> failwith "") in
    let rec absremover t =
     (TOP_DEPTH_CONV(absconv1 THENC BINOP_CONV (LAND_CONV POLY_CONV)) THENC
      TRY_CONV(absconv2 THENC NNF_NORM_CONV' THENC BINOP_CONV absremover)) t in
    let th0 = init_conv(mk_neg tm) in
    let tm0 = rand(concl th0) in
    let th =
      if tm0 = false_tm then fst(EQ_IMP_RULE th0) else
      let evs,bod = strip_exists tm0 in
      let avs,ibod = strip_forall bod in
      let th1 = itlist MK_FORALL avs (DEPTH_BINOP_CONV or_tm absremover ibod) in
      let th2 = overall [] [SPECL avs (ASSUME(rand(concl th1)))] in
      let th3 =
        itlist SIMPLE_CHOOSE evs (PROVE_HYP (EQ_MP th1 (ASSUME bod)) th2) in
      DISCH_ALL(PROVE_HYP (EQ_MP th0 (ASSUME (mk_neg tm))) th3) in
    MP (INST [tm,p_tm] pth_final) th;;

(* ------------------------------------------------------------------------- *)
(* Linear prover. This works over the rationals in general, but is designed  *)
(* to be OK on integers provided the input contains only integers.           *)
(* ------------------------------------------------------------------------- *)

let REAL_LINEAR_PROVER =
  let linear_add = combine (+/) (fun z -> z =/ num_0)
  and linear_cmul c = mapf (fun x -> c */ x)
  and one_tm = `&1` in
  let contradictory p (e,_) =
    (is_undefined e && not(p num_0)) ||
    (dom e = [one_tm] && not(p(apply e one_tm))) in
  let rec linear_ineqs vars (les,lts) =
    try find (contradictory (fun x -> x >/ num_0)) lts with Failure _ ->
    try find (contradictory (fun x -> x >=/ num_0)) les with Failure _ ->
    if vars = [] then failwith "linear_ineqs: no contradiction" else
    let ineqs = les @ lts in
    let blowup v =
      length(filter (fun (e,_) -> tryapplyd e v num_0 >/ num_0) ineqs) *
      length(filter (fun (e,_) -> tryapplyd e v num_0 </ num_0) ineqs) in
    let v =
     fst(hd(sort (fun (_,i) (_,j) -> i < j)
                 (map (fun v -> v,blowup v) vars))) in
    let addup (e1,p1) (e2,p2) acc =
      let c1 = tryapplyd e1 v num_0 and c2 = tryapplyd e2 v num_0 in
      if c1 */ c2 >=/ num_0 then acc else
      let e1' = linear_cmul (abs_num c2) e1
      and e2' = linear_cmul (abs_num c1) e2
      and p1' = Product(Rational_lt(abs_num c2),p1)
      and p2' = Product(Rational_lt(abs_num c1),p2) in
      (linear_add e1' e2',Sum(p1',p2'))::acc in
    let les0,les1 = partition (fun (e,_) -> tryapplyd e v num_0 =/ num_0) les
    and lts0,lts1 = partition (fun (e,_) -> tryapplyd e v num_0 =/ num_0) lts in
    let lesp,lesn = partition (fun (e,_) -> tryapplyd e v num_0 >/ num_0) les1
    and ltsp,ltsn = partition
     (fun (e,_) -> tryapplyd e v num_0 >/ num_0) lts1 in
    let les' = itlist (fun ep1 -> itlist (addup ep1) lesp) lesn les0
    and lts' = itlist (fun ep1 -> itlist (addup ep1) (lesp@ltsp)) ltsn
                      (itlist (fun ep1 -> itlist (addup ep1) (lesn@ltsn)) ltsp
                              lts0) in
    linear_ineqs (subtract vars [v]) (les',lts') in
  let rec linear_eqs(eqs,les,lts) =
    try find (contradictory (fun x -> x =/ num_0)) eqs with Failure _ ->
    match eqs with
      [] -> let vars = subtract
             (itlist (union o dom o fst) (les@lts) []) [one_tm] in
            linear_ineqs vars (les,lts)
    | (e,p)::es -> if is_undefined e then linear_eqs(es,les,lts) else
                   let x,c = choose (undefine one_tm e) in
                   let xform(t,q as inp) =
                     let d = tryapplyd t x num_0 in
                     if d =/ num_0 then inp else
                     let k = minus_num d */ abs_num c // c in
                     let e' = linear_cmul k e
                     and t' = linear_cmul (abs_num c) t
                     and p' = Eqmul(term_of_rat k,p)
                     and q' = Product(Rational_lt(abs_num c),q) in
                     linear_add e' t',Sum(p',q') in
                   linear_eqs(map xform es,map xform les,map xform lts) in
  let linear_prover =
   fun (eq,le,lt) ->
    let eqs = map2 (fun p n -> p,Axiom_eq n) eq (0--(length eq-1))
    and les = map2 (fun p n -> p,Axiom_le n) le (0--(length le-1))
    and lts = map2 (fun p n -> p,Axiom_lt n) lt (0--(length lt-1)) in
    linear_eqs(eqs,les,lts) in
  let lin_of_hol =
    let one_tm = `&1`
    and zero_tm = `&0`
    and add_tm = `(+):real->real->real`
    and mul_tm = `(*):real->real->real` in
    let rec lin_of_hol tm =
      if tm = zero_tm then undefined
      else if not (is_comb tm) then (tm |=> num 1)
      else if is_ratconst tm then (one_tm |=> rat_of_term tm) else
      let lop,r = dest_comb tm in
      if not (is_comb lop) then (tm |=> num 1) else
      let op,l = dest_comb lop in
      if op = add_tm then linear_add (lin_of_hol l) (lin_of_hol r)
      else if op = mul_tm && is_ratconst l then (r |=> rat_of_term l)
      else (tm |=> num 1) in
    lin_of_hol in
  let is_alien tm =
    match tm with
      Comb(Const("real_of_num",_),n) when not(is_numeral n) -> true
    | _ -> false in
  let is_suc_alien tm =
    match tm with
      Comb(Const("real_of_num",_),Comb(Const("SUC",_),_)) -> true
    | _ -> false in
  let dest_suc_alien tm =
    match tm with
      Comb(Const("real_of_num",_),Comb(Const("SUC",_),n)) -> n
    | _ -> failwith "" in
  let n_tm = `n:num` in
  let pth = REWRITE_RULE[GSYM real_ge] (SPEC n_tm REAL_POS) in
  let pth_suc = REWRITE_RULE[GSYM real_gt] (SPEC n_tm REAL_POS_LT) in
  fun translator (eq,le,lt) ->
    let eq_pols = map (lin_of_hol o lhand o concl) eq
    and le_pols = map (lin_of_hol o lhand o concl) le
    and lt_pols = map (lin_of_hol o lhand o concl) lt in
    let all_aliens = filter is_alien
      (itlist (union o dom) (eq_pols @ le_pols @ lt_pols) []) in
    let suc_aliens,aliens = partition is_suc_alien all_aliens in
    let le_pols' = le_pols @ map (fun v -> (v |=> num 1)) aliens in
    let lt_pols' = lt_pols @ map (fun v -> (v |=> num 1)) suc_aliens in
    let _,proof = linear_prover(eq_pols,le_pols',lt_pols') in
    let le' = le @ map (fun a -> INST [rand a,n_tm] pth) aliens in
    let lt' = lt @ map (fun a -> INST [dest_suc_alien a,n_tm] pth_suc) suc_aliens in
    translator (eq,le',lt') proof;;

(* ------------------------------------------------------------------------- *)
(* Bootstrapping REAL_ARITH: trivial abs-elim and only integer constants.    *)
(* ------------------------------------------------------------------------- *)

let REAL_ARITH =
  let REAL_POLY_NEG_CONV,REAL_POLY_ADD_CONV,REAL_POLY_SUB_CONV,
    REAL_POLY_MUL_CONV,REAL_POLY_POW_CONV,REAL_POLY_CONV =
  SEMIRING_NORMALIZERS_CONV REAL_POLY_CLAUSES REAL_POLY_NEG_CLAUSES
   (is_realintconst,
    REAL_INT_ADD_CONV,REAL_INT_MUL_CONV,REAL_INT_POW_CONV)
   (<) in
  let rule =
   GEN_REAL_ARITH
   (mk_realintconst,
    REAL_INT_EQ_CONV,REAL_INT_GE_CONV,REAL_INT_GT_CONV,
    REAL_POLY_CONV,REAL_POLY_NEG_CONV,REAL_POLY_ADD_CONV,REAL_POLY_MUL_CONV,
    NO_CONV,NO_CONV,REAL_LINEAR_PROVER)
  and deabs_conv = REWRITE_CONV[real_abs; real_max; real_min] in
  fun tm ->
    let th1 = deabs_conv tm in
    EQ_MP (SYM th1) (rule(rand(concl th1)));;

(* ------------------------------------------------------------------------- *)
(* Slightly less parametrized GEN_REAL_ARITH with more intelligent           *)
(* elimination of abs, max and min hardwired in.                             *)
(* ------------------------------------------------------------------------- *)

let GEN_REAL_ARITH =
  let ABSMAXMIN_ELIM_CONV1 =
    GEN_REWRITE_CONV I [time REAL_ARITH
     `(--(&1) * abs(x) >= r <=>
       --(&1) * x >= r /\ &1 * x >= r) /\
      (--(&1) * abs(x) + a >= r <=>
       a + --(&1) * x >= r /\ a + &1 * x >= r) /\
      (a + --(&1) * abs(x) >= r <=>
       a + --(&1) * x >= r /\ a + &1 * x >= r) /\
      (a + --(&1) * abs(x) + b >= r <=>
       a + --(&1) * x + b >= r /\ a + &1 * x + b >= r) /\
      (a + b + --(&1) * abs(x) >= r <=>
       a + b + --(&1) * x >= r /\ a + b + &1 * x >= r) /\
      (a + b + --(&1) * abs(x) + c >= r <=>
       a + b + --(&1) * x + c >= r /\ a + b + &1 * x + c >= r) /\
      (--(&1) * max x y >= r <=>
       --(&1) * x >= r /\ --(&1) * y >= r) /\
      (--(&1) * max x y + a >= r <=>
       a + --(&1) * x >= r /\ a + --(&1) * y >= r) /\
      (a + --(&1) * max x y >= r <=>
       a + --(&1) * x >= r /\ a + --(&1) * y >= r) /\
      (a + --(&1) * max x y + b >= r <=>
       a + --(&1) * x + b >= r /\ a + --(&1) * y  + b >= r) /\
      (a + b + --(&1) * max x y >= r <=>
       a + b + --(&1) * x >= r /\ a + b + --(&1) * y >= r) /\
      (a + b + --(&1) * max x y + c >= r <=>
       a + b + --(&1) * x + c >= r /\ a + b + --(&1) * y  + c >= r) /\
      (&1 * min x y >= r <=>
       &1 * x >= r /\ &1 * y >= r) /\
      (&1 * min x y + a >= r <=>
       a + &1 * x >= r /\ a + &1 * y >= r) /\
      (a + &1 * min x y >= r <=>
       a + &1 * x >= r /\ a + &1 * y >= r) /\
      (a + &1 * min x y + b >= r <=>
       a + &1 * x + b >= r /\ a + &1 * y  + b >= r) /\
      (a + b + &1 * min x y >= r <=>
       a + b + &1 * x >= r /\ a + b + &1 * y >= r) /\
      (a + b + &1 * min x y + c >= r <=>
       a + b + &1 * x + c >= r /\ a + b + &1 * y  + c >= r) /\
      (min x y >= r <=>
        x >= r /\  y >= r) /\
      (min x y + a >= r <=>
       a + x >= r /\ a + y >= r) /\
      (a + min x y >= r <=>
       a + x >= r /\ a + y >= r) /\
      (a + min x y + b >= r <=>
       a + x + b >= r /\ a + y  + b >= r) /\
      (a + b + min x y >= r <=>
       a + b + x >= r /\ a + b + y >= r) /\
      (a + b + min x y + c >= r <=>
       a + b + x + c >= r /\ a + b + y + c >= r) /\
      (--(&1) * abs(x) > r <=>
       --(&1) * x > r /\ &1 * x > r) /\
      (--(&1) * abs(x) + a > r <=>
       a + --(&1) * x > r /\ a + &1 * x > r) /\
      (a + --(&1) * abs(x) > r <=>
       a + --(&1) * x > r /\ a + &1 * x > r) /\
      (a + --(&1) * abs(x) + b > r <=>
       a + --(&1) * x + b > r /\ a + &1 * x + b > r) /\
      (a + b + --(&1) * abs(x) > r <=>
       a + b + --(&1) * x > r /\ a + b + &1 * x > r) /\
      (a + b + --(&1) * abs(x) + c > r <=>
       a + b + --(&1) * x + c > r /\ a + b + &1 * x + c > r) /\
      (--(&1) * max x y > r <=>
       --(&1) * x > r /\ --(&1) * y > r) /\
      (--(&1) * max x y + a > r <=>
       a + --(&1) * x > r /\ a + --(&1) * y > r) /\
      (a + --(&1) * max x y > r <=>
       a + --(&1) * x > r /\ a + --(&1) * y > r) /\
      (a + --(&1) * max x y + b > r <=>
       a + --(&1) * x + b > r /\ a + --(&1) * y  + b > r) /\
      (a + b + --(&1) * max x y > r <=>
       a + b + --(&1) * x > r /\ a + b + --(&1) * y > r) /\
      (a + b + --(&1) * max x y + c > r <=>
       a + b + --(&1) * x + c > r /\ a + b + --(&1) * y  + c > r) /\
      (min x y > r <=>
        x > r /\  y > r) /\
      (min x y + a > r <=>
       a + x > r /\ a + y > r) /\
      (a + min x y > r <=>
       a + x > r /\ a + y > r) /\
      (a + min x y + b > r <=>
       a + x + b > r /\ a + y  + b > r) /\
      (a + b + min x y > r <=>
       a + b + x > r /\ a + b + y > r) /\
      (a + b + min x y + c > r <=>
       a + b + x + c > r /\ a + b + y + c > r)`]
  and ABSMAXMIN_ELIM_CONV2 =
    let pth_abs = prove
     (`P(abs x) <=> (x >= &0 /\ P x) \/ (&0 > x /\ P (--x))`,
      REWRITE_TAC[real_abs; real_gt; real_ge] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[real_lt])
    and pth_max = prove
     (`P(max x y) <=> (y >= x /\ P y) \/ (x > y /\ P x)`,
      REWRITE_TAC[real_max; real_gt; real_ge] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[real_lt])
    and pth_min = prove
    (`P(min x y) <=> (y >= x /\ P x) \/ (x > y /\ P y)`,
      REWRITE_TAC[real_min; real_gt; real_ge] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[real_lt])
    and abs_tm = `real_abs`
    and p_tm = `P:real->bool`
    and x_tm = `x:real`
    and y_tm = `y:real` in
    let is_max = is_binop `real_max`
    and is_min = is_binop `real_min`
    and is_abs t = is_comb t && rator t = abs_tm in
    let eliminate_construct p c tm =
      let t = find_term (fun t -> p t && free_in t tm) tm in
      let v = genvar(type_of t) in
      let th0 = SYM(BETA_CONV(mk_comb(mk_abs(v,subst[v,t] tm),t))) in
      let p,ax = dest_comb(rand(concl th0)) in
      CONV_RULE(RAND_CONV(BINOP_CONV(RAND_CONV BETA_CONV)))
               (TRANS th0 (c p ax)) in
    let elim_abs =
      eliminate_construct is_abs
        (fun p ax -> INST [p,p_tm; rand ax,x_tm] pth_abs)
    and elim_max =
      eliminate_construct is_max
        (fun p ax -> let ax,y = dest_comb ax in
                     INST [p,p_tm; rand ax,x_tm; y,y_tm] pth_max)
    and elim_min =
      eliminate_construct is_min
        (fun p ax -> let ax,y = dest_comb ax in
                     INST [p,p_tm; rand ax,x_tm; y,y_tm] pth_min) in
    FIRST_CONV [elim_abs; elim_max; elim_min] in
  fun (mkconst,EQ,GE,GT,NORM,NEG,ADD,MUL,PROVER) ->
        GEN_REAL_ARITH(mkconst,EQ,GE,GT,NORM,NEG,ADD,MUL,
                       ABSMAXMIN_ELIM_CONV1,ABSMAXMIN_ELIM_CONV2,PROVER);;

(* ------------------------------------------------------------------------- *)
(* Incorporate that. This gets overwritten again in "calc_rat.ml".           *)
(* ------------------------------------------------------------------------- *)

let REAL_ARITH =
  let REAL_POLY_NEG_CONV,REAL_POLY_ADD_CONV,REAL_POLY_SUB_CONV,
    REAL_POLY_MUL_CONV,REAL_POLY_POW_CONV,REAL_POLY_CONV =
  SEMIRING_NORMALIZERS_CONV REAL_POLY_CLAUSES REAL_POLY_NEG_CLAUSES
   (is_realintconst,
    REAL_INT_ADD_CONV,REAL_INT_MUL_CONV,REAL_INT_POW_CONV)
   (<) in
  GEN_REAL_ARITH
   (mk_realintconst,
    REAL_INT_EQ_CONV,REAL_INT_GE_CONV,REAL_INT_GT_CONV,
    REAL_POLY_CONV,REAL_POLY_NEG_CONV,REAL_POLY_ADD_CONV,REAL_POLY_MUL_CONV,
    REAL_LINEAR_PROVER);;
