(* ========================================================================= *)
(* Relatively efficient HOL conversions for canonical polynomial form.       *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "calc_num.ml";;

let SEMIRING_NORMALIZERS_CONV =
  let SEMIRING_PTHS = prove
   (`(!x:A y z. add x (add y z) = add (add x y) z) /\
     (!x y. add x y = add y x) /\
     (!x. add r0 x = x) /\
     (!x y z. mul x (mul y z) = mul (mul x y) z) /\
     (!x y. mul x y = mul y x) /\
     (!x. mul r1 x = x) /\
     (!x. mul r0 x = r0) /\
     (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
     (!x. pwr x 0 = r1) /\
     (!x n. pwr x (SUC n) = mul x (pwr x n))
     ==> (mul r1 x = x) /\
         (add (mul a m) (mul b m) = mul (add a b) m) /\
         (add (mul a m) m = mul (add a r1) m) /\
         (add m (mul a m) = mul (add a r1) m) /\
         (add m m = mul (add r1 r1) m) /\
         (mul r0 m = r0) /\
         (add r0 a = a) /\
         (add a r0 = a) /\
         (mul a b = mul b a) /\
         (mul (add a b) c = add (mul a c) (mul b c)) /\
         (mul r0 a = r0) /\
         (mul a r0 = r0) /\
         (mul r1 a = a) /\
         (mul a r1 = a) /\
         (mul (mul lx ly) (mul rx ry) = mul (mul lx rx) (mul ly ry)) /\
         (mul (mul lx ly) (mul rx ry) = mul lx (mul ly (mul rx ry))) /\
         (mul (mul lx ly) (mul rx ry) = mul rx (mul (mul lx ly) ry)) /\
         (mul (mul lx ly) rx = mul (mul lx rx) ly) /\
         (mul (mul lx ly) rx = mul lx (mul ly rx)) /\
         (mul lx rx = mul rx lx) /\
         (mul lx (mul rx ry) = mul (mul lx rx) ry) /\
         (mul lx (mul rx ry) = mul rx (mul lx ry)) /\
         (add (add a b) (add c d) = add (add a c) (add b d)) /\
         (add (add a b) c = add a (add b c)) /\
         (add a (add c d) = add c (add a d)) /\
         (add (add a b) c = add (add a c) b) /\
         (add a c = add c a) /\
         (add a (add c d) = add (add a c) d) /\
         (mul (pwr x p) (pwr x q) = pwr x (p + q)) /\
         (mul x (pwr x q) = pwr x (SUC q)) /\
         (mul (pwr x q) x = pwr x (SUC q)) /\
         (mul x x = pwr x 2) /\
         (pwr (mul x y) q = mul (pwr x q) (pwr y q)) /\
         (pwr (pwr x p) q = pwr x (p * q)) /\
         (pwr x 0 = r1) /\
         (pwr x 1 = x) /\
         (mul x (add y z) = add (mul x y) (mul x z)) /\
         (pwr x (SUC q) = mul x (pwr x q))`,
    STRIP_TAC THEN
    SUBGOAL_THEN
     `(!m:A n. add m n = add n m) /\
      (!m n p. add (add m n) p = add m (add n p)) /\
      (!m n p. add m (add n p) = add n (add m p)) /\
      (!x. add x r0 = x) /\
      (!m n. mul m n = mul n m) /\
      (!m n p. mul (mul m n) p = mul m (mul n p)) /\
      (!m n p. mul m (mul n p) = mul n (mul m p)) /\
      (!m n p. mul (add m n) p = add (mul m p) (mul n p)) /\
      (!x. mul x r1 = x) /\
      (!x. mul x r0 = r0)`
    MP_TAC THENL
     [ASM_MESON_TAC[];
      MAP_EVERY (fun t -> UNDISCH_THEN t (K ALL_TAC))
       [`!x:A y z. add x (add y z) = add (add x y) z`;
        `!x:A y. add x y :A = add y x`;
        `!x:A y z. mul x (mul y z) = mul (mul x y) z`;
        `!x:A y. mul x y :A = mul y x`] THEN
      STRIP_TAC] THEN
    ASM_REWRITE_TAC[num_CONV `2`; num_CONV `1`] THEN
    SUBGOAL_THEN `!m n:num x:A. pwr x (m + n) :A = mul (pwr x m) (pwr x n)`
    ASSUME_TAC THENL
     [GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
    SUBGOAL_THEN `!x:A y:A n:num. pwr (mul x y) n = mul (pwr x n) (pwr y n)`
    ASSUME_TAC THENL
     [GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!x:A m:num n. pwr (pwr x m) n = pwr x (m * n)`
     (fun th -> ASM_MESON_TAC[th]) THEN
    GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES])
  and true_tm = concl TRUTH in
  fun sth rth (is_semiring_constant,
               SEMIRING_ADD_CONV,
               SEMIRING_MUL_CONV,
               SEMIRING_POW_CONV) ->
    let
     [pthm_01; pthm_02; pthm_03; pthm_04; pthm_05; pthm_06; pthm_07; pthm_08;
      pthm_09; pthm_10; pthm_11; pthm_12; pthm_13; pthm_14; pthm_15; pthm_16;
      pthm_17; pthm_18; pthm_19; pthm_20; pthm_21; pthm_22; pthm_23; pthm_24;
      pthm_25; pthm_26; pthm_27; pthm_28; pthm_29; pthm_30; pthm_31; pthm_32;
      pthm_33; pthm_34; pthm_35; pthm_36; pthm_37; pthm_38] =
     CONJUNCTS(MATCH_MP SEMIRING_PTHS sth) in
    let add_tm = rator(rator(lhand(concl pthm_07)))
    and mul_tm = rator(rator(lhand(concl pthm_13)))
    and pow_tm = rator(rator(rand(concl pthm_32)))
    and zero_tm = rand(concl pthm_06)
    and one_tm = rand(lhand(concl pthm_14))
    and ty = type_of(rand(concl pthm_01)) in

    let p_tm = `p:num`
    and q_tm = `q:num`
    and zeron_tm = `0`
    and onen_tm = `1`
    and a_tm = mk_var("a",ty)
    and b_tm = mk_var("b",ty)
    and c_tm = mk_var("c",ty)
    and d_tm = mk_var("d",ty)
    and lx_tm = mk_var("lx",ty)
    and ly_tm = mk_var("ly",ty)
    and m_tm = mk_var("m",ty)
    and rx_tm = mk_var("rx",ty)
    and ry_tm = mk_var("ry",ty)
    and x_tm = mk_var("x",ty)
    and y_tm = mk_var("y",ty)
    and z_tm = mk_var("z",ty) in

    let dest_add = dest_binop add_tm
    and dest_mul = dest_binop mul_tm
    and dest_pow tm =
      let l,r = dest_binop pow_tm tm in
      if is_numeral r then l,r else failwith "dest_pow"
    and is_add = is_binop add_tm
    and is_mul = is_binop mul_tm in

    let nthm_1,nthm_2,sub_tm,neg_tm,dest_sub,is_sub =
      if concl rth = true_tm then rth,rth,true_tm,true_tm,
                     (fun t -> t,t),K false
      else
        let nthm_1 = SPEC x_tm (CONJUNCT1 rth)
        and nthm_2 = SPECL [x_tm; y_tm] (CONJUNCT2 rth) in
        let sub_tm = rator(rator(lhand(concl nthm_2)))
        and neg_tm = rator(lhand(concl nthm_1)) in
        let dest_sub = dest_binop sub_tm
        and is_sub = is_binop sub_tm in
        (nthm_1,nthm_2,sub_tm,neg_tm,dest_sub,is_sub) in

    fun variable_order ->

(* ------------------------------------------------------------------------- *)
(* Conversion for "x^n * x^m", with either x^n = x and/or x^m = x possible.  *)
(* Also deals with "const * const", but both terms must involve powers of    *)
(* the same variable, or both be constants, or behaviour may be incorrect.   *)
(* ------------------------------------------------------------------------- *)

    let POWVAR_MUL_CONV tm =
      let l,r = dest_mul tm in
      if is_semiring_constant l && is_semiring_constant r
      then SEMIRING_MUL_CONV tm else
      try let lx,ln = dest_pow l in
          try let rx,rn = dest_pow r in
              let th1 = INST [lx,x_tm; ln,p_tm; rn,q_tm] pthm_29 in
              let tm1,tm2 = dest_comb(rand(concl th1)) in
              TRANS th1 (AP_TERM tm1 (NUM_ADD_CONV tm2))
          with Failure _ ->
              let th1 = INST [lx,x_tm; ln,q_tm] pthm_31 in
              let tm1,tm2 = dest_comb(rand(concl th1)) in
              TRANS th1 (AP_TERM tm1 (NUM_SUC_CONV tm2))
      with Failure _ ->
          try let rx,rn = dest_pow r in
              let th1 = INST [rx,x_tm; rn,q_tm] pthm_30 in
              let tm1,tm2 = dest_comb(rand(concl th1)) in
              TRANS th1 (AP_TERM tm1 (NUM_SUC_CONV tm2))
          with Failure _ ->
              INST [l,x_tm] pthm_32 in

(* ------------------------------------------------------------------------- *)
(* Remove "1 * m" from a monomial, and just leave m.                         *)
(* ------------------------------------------------------------------------- *)

    let MONOMIAL_DEONE th =
      try let l,r = dest_mul(rand(concl th)) in
          if l = one_tm then TRANS th (INST [r,x_tm] pthm_01) else th
      with Failure _ -> th in

(* ------------------------------------------------------------------------- *)
(* Conversion for "(monomial)^n", where n is a numeral.                      *)
(* ------------------------------------------------------------------------- *)

    let MONOMIAL_POW_CONV =
      let rec MONOMIAL_POW tm bod ntm =
        if not(is_comb bod) then REFL tm
        else if is_semiring_constant bod then SEMIRING_POW_CONV tm else
        let lop,r = dest_comb bod in
        if not(is_comb lop) then REFL tm else
        let op,l = dest_comb lop in
        if op = pow_tm && is_numeral r then
          let th1 = INST [l,x_tm; r,p_tm; ntm,q_tm] pthm_34 in
          let l,r = dest_comb(rand(concl th1)) in
          TRANS th1 (AP_TERM l (NUM_MULT_CONV r))
        else if op = mul_tm then
          let th1 = INST [l,x_tm; r,y_tm; ntm,q_tm] pthm_33 in
          let xy,z = dest_comb(rand(concl th1)) in
          let x,y = dest_comb xy in
          let thl = MONOMIAL_POW y l ntm
          and thr = MONOMIAL_POW z r ntm in
          TRANS th1 (MK_COMB(AP_TERM x thl,thr))
        else REFL tm in
      fun tm ->
        let lop,r = dest_comb tm in
        let op,l = dest_comb lop in
        if op <> pow_tm || not(is_numeral r) then failwith "MONOMIAL_POW_CONV"
        else if r = zeron_tm then INST [l,x_tm] pthm_35
        else if r = onen_tm then INST [l,x_tm] pthm_36
        else MONOMIAL_DEONE(MONOMIAL_POW tm l r) in

(* ------------------------------------------------------------------------- *)
(* Multiplication of canonical monomials.                                    *)
(* ------------------------------------------------------------------------- *)

    let MONOMIAL_MUL_CONV =
      let powvar tm =
        if is_semiring_constant tm then one_tm else
        try let lop,r = dest_comb tm in
            let op,l = dest_comb lop in
            if op = pow_tm && is_numeral r then l else failwith ""
        with Failure _ -> tm in
      let vorder x y =
        if x = y then 0
        else if x = one_tm then -1
        else if y = one_tm then 1
        else if variable_order x y then -1 else 1 in
      let rec MONOMIAL_MUL tm l r =
        try let lx,ly = dest_mul l in
            let vl = powvar lx in
            try let rx,ry = dest_mul r in
                let vr = powvar rx in
                let ord = vorder vl vr in
                if ord = 0 then
                  let th1 = INST
                    [lx,lx_tm; ly,ly_tm; rx,rx_tm; ry,ry_tm] pthm_15 in
                  let tm1,tm2 = dest_comb(rand(concl th1)) in
                  let tm3,tm4 = dest_comb tm1 in
                  let th2 = AP_THM (AP_TERM tm3 (POWVAR_MUL_CONV tm4)) tm2 in
                  let th3 = TRANS th1 th2 in
                  let tm5,tm6 = dest_comb(rand(concl th3)) in
                  let tm7,tm8 = dest_comb tm6 in
                  let th4 = MONOMIAL_MUL tm6 (rand tm7) tm8 in
                  TRANS th3 (AP_TERM tm5 th4)
                else
                  let th0 = if ord < 0 then pthm_16 else pthm_17 in
                  let th1 = INST
                    [lx,lx_tm; ly,ly_tm; rx,rx_tm; ry,ry_tm] th0 in
                  let tm1,tm2 = dest_comb(rand(concl th1)) in
                  let tm3,tm4 = dest_comb tm2 in
                  TRANS th1 (AP_TERM tm1 (MONOMIAL_MUL tm2 (rand tm3) tm4))
            with Failure _ ->
                let vr = powvar r in
                let ord = vorder vl vr in
                if ord = 0 then
                  let th1 = INST [lx,lx_tm; ly,ly_tm; r,rx_tm] pthm_18 in
                  let tm1,tm2 = dest_comb(rand(concl th1)) in
                  let tm3,tm4 = dest_comb tm1 in
                  let th2 = AP_THM (AP_TERM tm3 (POWVAR_MUL_CONV tm4)) tm2 in
                  TRANS th1 th2
                else if ord < 0 then
                  let th1 = INST [lx,lx_tm; ly,ly_tm; r,rx_tm] pthm_19 in
                  let tm1,tm2 = dest_comb(rand(concl th1)) in
                  let tm3,tm4 = dest_comb tm2 in
                  TRANS th1 (AP_TERM tm1 (MONOMIAL_MUL tm2 (rand tm3) tm4))
                else INST [l,lx_tm; r,rx_tm] pthm_20
        with Failure _ ->
            let vl = powvar l in
            try let rx,ry = dest_mul r in
                let vr = powvar rx in
                let ord = vorder vl vr in
                if ord = 0 then
                  let th1 = INST [l,lx_tm; rx,rx_tm; ry,ry_tm] pthm_21 in
                  let tm1,tm2 = dest_comb(rand(concl th1)) in
                  let tm3,tm4 = dest_comb tm1 in
                  TRANS th1 (AP_THM (AP_TERM tm3 (POWVAR_MUL_CONV tm4)) tm2)
                else if ord > 0 then
                  let th1 = INST [l,lx_tm; rx,rx_tm; ry,ry_tm] pthm_22 in
                  let tm1,tm2 = dest_comb(rand(concl th1)) in
                  let tm3,tm4 = dest_comb tm2 in
                  TRANS th1 (AP_TERM tm1 (MONOMIAL_MUL tm2 (rand tm3) tm4))
                else REFL tm
            with Failure _ ->
                let vr = powvar r in
                let ord = vorder vl vr in
                if ord = 0 then POWVAR_MUL_CONV tm
                else if ord > 0 then INST [l,lx_tm; r,rx_tm] pthm_20
                else REFL tm in
      fun tm -> let l,r = dest_mul tm in MONOMIAL_DEONE(MONOMIAL_MUL tm l r) in

(* ------------------------------------------------------------------------- *)
(* Multiplication by monomial of a polynomial.                               *)
(* ------------------------------------------------------------------------- *)

    let POLYNOMIAL_MONOMIAL_MUL_CONV =
      let rec PMM_CONV tm =
        let l,r = dest_mul tm in
        try let y,z = dest_add r in
            let th1 = INST [l,x_tm; y,y_tm; z,z_tm] pthm_37 in
            let tm1,tm2 = dest_comb(rand(concl th1)) in
            let tm3,tm4 = dest_comb tm1 in
            let th2 = MK_COMB(AP_TERM tm3 (MONOMIAL_MUL_CONV tm4),
                              PMM_CONV tm2) in
            TRANS th1 th2
        with Failure _ -> MONOMIAL_MUL_CONV tm in
      PMM_CONV in

(* ------------------------------------------------------------------------- *)
(* Addition of two monomials identical except for constant multiples.        *)
(* ------------------------------------------------------------------------- *)

    let MONOMIAL_ADD_CONV tm =
      let l,r = dest_add tm in
      if is_semiring_constant l && is_semiring_constant r
      then SEMIRING_ADD_CONV tm else
      let th1 =
        if is_mul l && is_semiring_constant(lhand l) then
          if is_mul r && is_semiring_constant(lhand r) then
            INST [lhand l,a_tm; lhand r,b_tm; rand r,m_tm] pthm_02
          else
            INST [lhand l,a_tm; r,m_tm] pthm_03
        else
          if is_mul r && is_semiring_constant(lhand r) then
            INST [lhand r,a_tm; l,m_tm] pthm_04
          else
            INST [r,m_tm] pthm_05 in
      let tm1,tm2 = dest_comb(rand(concl th1)) in
      let tm3,tm4 = dest_comb tm1 in
      let th2 = AP_TERM tm3 (SEMIRING_ADD_CONV tm4) in
      let th3 = TRANS th1 (AP_THM th2 tm2) in
      let tm5 = rand(concl th3) in
      if lhand tm5 = zero_tm then TRANS th3 (INST [rand tm5,m_tm] pthm_06)
      else MONOMIAL_DEONE th3 in

(* ------------------------------------------------------------------------- *)
(* Ordering on monomials.                                                    *)
(* ------------------------------------------------------------------------- *)

    let powervars tm =
      let ptms = striplist dest_mul tm in
      if is_semiring_constant (hd ptms) then tl ptms else ptms in

    let dest_varpow tm =
      try let x,n = dest_pow tm in (x,dest_numeral n)
      with Failure _ ->
       (tm,(if is_semiring_constant tm then num_0 else num_1)) in

    let morder =
      let rec lexorder l1 l2 =
        match (l1,l2) with
          [],[] -> 0
        | vps,[] -> -1
        | [],vps -> 1
        | ((x1,n1)::vs1),((x2,n2)::vs2) ->
              if variable_order x1 x2 then 1
              else if variable_order x2 x1 then -1
              else if n1 </ n2 then -1
              else if n2 </ n1 then 1
              else lexorder vs1 vs2 in
      fun tm1 tm2 ->
        let vdegs1 = map dest_varpow (powervars tm1)
        and vdegs2 = map dest_varpow (powervars tm2) in
        let deg1 = itlist ((+/) o snd) vdegs1 num_0
        and deg2 = itlist ((+/) o snd) vdegs2 num_0 in
        if deg1 </ deg2 then -1 else if deg1 >/ deg2 then 1
        else lexorder vdegs1 vdegs2 in

(* ------------------------------------------------------------------------- *)
(* Addition of two polynomials.                                              *)
(* ------------------------------------------------------------------------- *)

    let POLYNOMIAL_ADD_CONV =
      let DEZERO_RULE th =
        let tm = rand(concl th) in
        if not(is_add tm) then th else
        let lop,r = dest_comb tm in
        let l = rand lop in
        if l = zero_tm then TRANS th (INST [r,a_tm] pthm_07)
        else if r = zero_tm then TRANS th (INST [l,a_tm] pthm_08)
        else th in
      let rec PADD tm =
        let l,r = dest_add tm in
        if l = zero_tm then INST [r,a_tm] pthm_07
        else if r = zero_tm then INST [l,a_tm] pthm_08 else
        if is_add l then
          let a,b = dest_add l in
          if is_add r then
            let c,d = dest_add r in
            let ord = morder a c in
            if ord = 0 then
              let th1 = INST [a,a_tm; b,b_tm; c,c_tm; d,d_tm] pthm_23 in
              let tm1,tm2 = dest_comb(rand(concl th1)) in
              let tm3,tm4 = dest_comb tm1 in
              let th2 = AP_TERM tm3 (MONOMIAL_ADD_CONV tm4) in
              DEZERO_RULE (TRANS th1 (MK_COMB(th2,PADD tm2)))
            else
              let th1 =
                if ord > 0 then INST [a,a_tm; b,b_tm; r,c_tm] pthm_24
                else INST [l,a_tm; c,c_tm; d,d_tm] pthm_25 in
              let tm1,tm2 = dest_comb(rand(concl th1)) in
              DEZERO_RULE (TRANS th1 (AP_TERM tm1 (PADD tm2)))
          else
            let ord = morder a r in
            if ord = 0 then
              let th1 = INST [a,a_tm; b,b_tm; r,c_tm] pthm_26 in
              let tm1,tm2 = dest_comb(rand(concl th1)) in
              let tm3,tm4 = dest_comb tm1 in
              let th2 = AP_THM (AP_TERM tm3 (MONOMIAL_ADD_CONV tm4)) tm2 in
              DEZERO_RULE (TRANS th1 th2)
            else if ord > 0 then
              let th1 = INST [a,a_tm; b,b_tm; r,c_tm] pthm_24 in
              let tm1,tm2 = dest_comb(rand(concl th1)) in
              DEZERO_RULE (TRANS th1 (AP_TERM tm1 (PADD tm2)))
            else
              DEZERO_RULE (INST [l,a_tm; r,c_tm] pthm_27)
        else
          if is_add r then
            let c,d = dest_add r in
            let ord = morder l c in
            if ord = 0 then
              let th1 = INST [l,a_tm; c,c_tm; d,d_tm] pthm_28 in
              let tm1,tm2 = dest_comb(rand(concl th1)) in
              let tm3,tm4 = dest_comb tm1 in
              let th2 = AP_THM (AP_TERM tm3 (MONOMIAL_ADD_CONV tm4)) tm2 in
              DEZERO_RULE (TRANS th1 th2)
            else if ord > 0 then
              REFL tm
            else
              let th1 = INST [l,a_tm; c,c_tm; d,d_tm] pthm_25 in
              let tm1,tm2 = dest_comb(rand(concl th1)) in
              DEZERO_RULE (TRANS th1 (AP_TERM tm1 (PADD tm2)))
          else
            let ord = morder l r in
            if ord = 0 then MONOMIAL_ADD_CONV tm
            else if ord > 0 then DEZERO_RULE(REFL tm)
            else DEZERO_RULE(INST [l,a_tm; r,c_tm] pthm_27) in
      PADD in

(* ------------------------------------------------------------------------- *)
(* Multiplication of two polynomials.                                        *)
(* ------------------------------------------------------------------------- *)

    let POLYNOMIAL_MUL_CONV =
      let rec PMUL tm =
        let l,r = dest_mul tm in
        if not(is_add l) then POLYNOMIAL_MONOMIAL_MUL_CONV tm
        else if not(is_add r) then
          let th1 = INST [l,a_tm; r,b_tm] pthm_09 in
          TRANS th1 (POLYNOMIAL_MONOMIAL_MUL_CONV(rand(concl th1)))
        else
          let a,b = dest_add l in
          let th1 = INST [a,a_tm; b,b_tm; r,c_tm] pthm_10 in
          let tm1,tm2 = dest_comb(rand(concl th1)) in
          let tm3,tm4 = dest_comb tm1 in
          let th2 = AP_TERM tm3 (POLYNOMIAL_MONOMIAL_MUL_CONV tm4) in
          let th3 = TRANS th1 (MK_COMB(th2,PMUL tm2)) in
          TRANS th3 (POLYNOMIAL_ADD_CONV (rand(concl th3))) in
      fun tm ->
        let l,r = dest_mul tm in
        if l = zero_tm then INST [r,a_tm] pthm_11
        else if r = zero_tm then INST [l,a_tm] pthm_12
        else if l = one_tm then INST [r,a_tm] pthm_13
        else if r = one_tm then INST [l,a_tm] pthm_14
        else PMUL tm in

(* ------------------------------------------------------------------------- *)
(* Power of polynomial (optimized for the monomial and trivial cases).       *)
(* ------------------------------------------------------------------------- *)

    let POLYNOMIAL_POW_CONV =
      let rec PPOW tm =
        let l,n = dest_pow tm in
        if n = zeron_tm then INST [l,x_tm] pthm_35
        else if n = onen_tm then INST [l,x_tm] pthm_36 else
        let th1 = num_CONV n in
        let th2 = INST [l,x_tm; rand(rand(concl th1)),q_tm] pthm_38 in
        let tm1,tm2 = dest_comb(rand(concl th2)) in
        let th3 = TRANS th2 (AP_TERM tm1 (PPOW tm2)) in
        let th4 = TRANS (AP_TERM (rator tm) th1) th3 in
        TRANS th4 (POLYNOMIAL_MUL_CONV (rand(concl th4))) in
      fun tm ->
        if is_add(lhand tm) then PPOW tm else MONOMIAL_POW_CONV tm in

(* ------------------------------------------------------------------------- *)
(* Negation.                                                                 *)
(* ------------------------------------------------------------------------- *)

    let POLYNOMIAL_NEG_CONV =
      fun tm ->
        let l,r = dest_comb tm in
        if l <> neg_tm then failwith "POLYNOMIAL_NEG_CONV" else
        let th1 = INST [r,x_tm] nthm_1 in
        TRANS th1 (POLYNOMIAL_MONOMIAL_MUL_CONV (rand(concl th1))) in

(* ------------------------------------------------------------------------- *)
(* Subtraction.                                                              *)
(* ------------------------------------------------------------------------- *)

    let POLYNOMIAL_SUB_CONV =
      fun tm ->
        let l,r = dest_sub tm in
        let th1 = INST [l,x_tm; r,y_tm] nthm_2 in
        let tm1,tm2 = dest_comb(rand(concl th1)) in
        let th2 = AP_TERM tm1 (POLYNOMIAL_MONOMIAL_MUL_CONV tm2) in
        TRANS th1 (TRANS th2 (POLYNOMIAL_ADD_CONV (rand(concl th2)))) in

(* ------------------------------------------------------------------------- *)
(* Conversion from HOL term.                                                 *)
(* ------------------------------------------------------------------------- *)

    let rec POLYNOMIAL_CONV tm =
      if not(is_comb tm) || is_semiring_constant tm then REFL tm else
      let lop,r = dest_comb tm in
      if lop = neg_tm then
         let th1 = AP_TERM lop (POLYNOMIAL_CONV r) in
         TRANS th1 (POLYNOMIAL_NEG_CONV (rand(concl th1)))
      else if not(is_comb lop) then REFL tm else
         let op,l = dest_comb lop in
         if op = pow_tm && is_numeral r then
           let th1 = AP_THM (AP_TERM op (POLYNOMIAL_CONV l)) r in
           TRANS th1 (POLYNOMIAL_POW_CONV (rand(concl th1)))
         else
           if op = add_tm || op = mul_tm || op = sub_tm then
             let th1 = MK_COMB(AP_TERM op (POLYNOMIAL_CONV l),
                               POLYNOMIAL_CONV r) in
             let fn = if op = add_tm then POLYNOMIAL_ADD_CONV
                      else if op = mul_tm then POLYNOMIAL_MUL_CONV
                      else POLYNOMIAL_SUB_CONV in
             TRANS th1 (fn (rand(concl th1)))
           else REFL tm in
    POLYNOMIAL_NEG_CONV,POLYNOMIAL_ADD_CONV,POLYNOMIAL_SUB_CONV,
    POLYNOMIAL_MUL_CONV,POLYNOMIAL_POW_CONV,POLYNOMIAL_CONV;;

(* ------------------------------------------------------------------------- *)
(* Instantiate it to the natural numbers.                                    *)
(* ------------------------------------------------------------------------- *)

let NUM_NORMALIZE_CONV =
  let sth = prove
   (`(!x y z. x + (y + z) = (x + y) + z) /\
     (!x y. x + y = y + x) /\
     (!x. 0 + x = x) /\
     (!x y z. x * (y * z) = (x * y) * z) /\
     (!x y. x * y = y * x) /\
     (!x. 1 * x = x) /\
     (!x. 0 * x = 0) /\
     (!x y z. x * (y + z) = x * y + x * z) /\
     (!x. x EXP 0 = 1) /\
     (!x n. x EXP (SUC n) = x * x EXP n)`,
    REWRITE_TAC[EXP; MULT_CLAUSES; ADD_CLAUSES; LEFT_ADD_DISTRIB] THEN
    REWRITE_TAC[ADD_AC; MULT_AC])
  and rth = TRUTH
  and is_semiring_constant = is_numeral
  and SEMIRING_ADD_CONV = NUM_ADD_CONV
  and SEMIRING_MUL_CONV = NUM_MULT_CONV
  and SEMIRING_POW_CONV = NUM_EXP_CONV in
  let _,_,_,_,_,NUM_NORMALIZE_CONV =
    SEMIRING_NORMALIZERS_CONV sth rth
     (is_semiring_constant,
      SEMIRING_ADD_CONV,SEMIRING_MUL_CONV,SEMIRING_POW_CONV)
     (<) in
  NUM_NORMALIZE_CONV;;
