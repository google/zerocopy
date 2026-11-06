(* ========================================================================= *)
(* Generic Grobner basis algorithm.                                          *)
(*                                                                           *)
(* Whatever the instantiation, it basically solves the universal theory of   *)
(* the complex numbers, or equivalently something like the theory of all     *)
(* commutative cancellation semirings with no nilpotent elements and having  *)
(* characteristic zero. We could do "all rings" by a more elaborate integer  *)
(* version of Grobner bases, but I don't have any useful applications.       *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "normalizer.ml";;

(* ------------------------------------------------------------------------- *)
(* Type for recording history, i.e. how a polynomial was obtained.           *)
(* ------------------------------------------------------------------------- *)

type history =
   Start of int
 | Mmul of (num * (int list)) * history
 | Add of history * history;;

(* ------------------------------------------------------------------------- *)
(* Overall function; everything else is local.                               *)
(* ------------------------------------------------------------------------- *)

let RING_AND_IDEAL_CONV =

  (* ----------------------------------------------------------------------- *)
  (* Monomial ordering.                                                      *)
  (* ----------------------------------------------------------------------- *)

  let morder_lt =
    let rec lexorder l1 l2 =
      match (l1,l2) with
          [],[] -> false
        | (x1::o1,x2::o2) -> x1 > x2 || x1 = x2 && lexorder o1 o2
        | _ -> failwith "morder: inconsistent monomial lengths" in
    fun m1 m2 -> let n1 = itlist (+) m1 0
                 and n2 = itlist (+) m2 0 in
                 n1 < n2 || n1 = n2 && lexorder m1 m2 in

  (* ----------------------------------------------------------------------- *)
  (* Arithmetic on canonical polynomials.                                    *)
  (* ----------------------------------------------------------------------- *)

  let grob_neg = map (fun (c,m) -> (minus_num c,m)) in

  let rec grob_add l1 l2 =
    match (l1,l2) with
      ([],l2) -> l2
    | (l1,[]) -> l1
    | ((c1,m1)::o1,(c2,m2)::o2) ->
          if m1 = m2 then
            let c = c1+/c2 and rest = grob_add o1 o2 in
            if c =/ num_0 then rest else (c,m1)::rest
          else if morder_lt m2 m1 then (c1,m1)::(grob_add o1 l2)
          else (c2,m2)::(grob_add l1 o2) in

  let grob_sub l1 l2 = grob_add l1 (grob_neg l2) in

  let grob_mmul (c1,m1) (c2,m2) = (c1*/c2,map2 (+) m1 m2) in

  let rec grob_cmul cm pol = map (grob_mmul cm) pol in

  let rec grob_mul l1 l2 =
    match l1 with
      [] -> []
    | (h1::t1) -> grob_add (grob_cmul h1 l2) (grob_mul t1 l2) in

  let grob_inv l =
    match l with
      [c,vs] when forall (fun x -> x = 0) vs ->
          if c =/ num_0 then failwith "grob_inv: division by zero"
          else [num_1 // c,vs]
    | _ -> failwith "grob_inv: non-constant divisor polynomial" in

  let grob_div l1 l2 =
    match l2 with
      [c,l] when forall (fun x -> x = 0) l ->
          if c =/ num_0 then failwith "grob_div: division by zero"
          else grob_cmul (num_1 // c,l) l1
    | _ -> failwith "grob_div: non-constant divisor polynomial" in

  let rec grob_pow vars l n =
    if n < 0 then failwith "grob_pow: negative power"
    else if n = 0 then [num_1,map (fun v -> 0) vars]
    else grob_mul l (grob_pow vars l (n - 1)) in

  (* ----------------------------------------------------------------------- *)
  (* Monomial division operation.                                            *)
  (* ----------------------------------------------------------------------- *)

  let mdiv (c1,m1) (c2,m2) =
    (c1//c2,
     map2 (fun n1 n2 -> if n1 < n2 then failwith "mdiv" else n1-n2) m1 m2) in

  (* ----------------------------------------------------------------------- *)
  (* Lowest common multiple of two monomials.                                *)
  (* ----------------------------------------------------------------------- *)

  let mlcm (c1,m1) (c2,m2) = (num_1,map2 max m1 m2) in

  (* ----------------------------------------------------------------------- *)
  (* Reduce monomial cm by polynomial pol, returning replacement for cm.     *)
  (* ----------------------------------------------------------------------- *)

  let reduce1 cm (pol,hpol) =
    match pol with
      [] -> failwith "reduce1"
    | cm1::cms -> try let (c,m) = mdiv cm cm1 in
                      (grob_cmul (minus_num c,m) cms,
                       Mmul((minus_num c,m),hpol))
                  with Failure _ -> failwith "reduce1" in

  (* ----------------------------------------------------------------------- *)
  (* Try this for all polynomials in a basis.                                *)
  (* ----------------------------------------------------------------------- *)

  let reduceb cm basis = tryfind (fun p -> reduce1 cm p) basis in

  (* ----------------------------------------------------------------------- *)
  (* Reduction of a polynomial (always picking largest monomial possible).   *)
  (* ----------------------------------------------------------------------- *)

  let rec reduce basis (pol,hist) =
    match pol with
      [] -> (pol,hist)
    | cm::ptl -> try let q,hnew = reduceb cm basis in
                     reduce basis (grob_add q ptl,Add(hnew,hist))
                 with Failure _ ->
                     let q,hist' = reduce basis (ptl,hist) in
                     cm::q,hist' in

  (* ----------------------------------------------------------------------- *)
  (* Check for orthogonality w.r.t. LCM.                                     *)
  (* ----------------------------------------------------------------------- *)

  let orthogonal l p1 p2 =
    snd l = snd(grob_mmul (hd p1) (hd p2)) in

  (* ----------------------------------------------------------------------- *)
  (* Compute S-polynomial of two polynomials.                                *)
  (* ----------------------------------------------------------------------- *)

  let spoly cm ph1 ph2 =
    match (ph1,ph2) with
      ([],h),p -> ([],h)
    | p,([],h) -> ([],h)
    | (cm1::ptl1,his1),(cm2::ptl2,his2) ->
          (grob_sub (grob_cmul (mdiv cm cm1) ptl1)
                    (grob_cmul (mdiv cm cm2) ptl2),
           Add(Mmul(mdiv cm cm1,his1),
               Mmul(mdiv (minus_num(fst cm),snd cm) cm2,his2))) in

  (* ----------------------------------------------------------------------- *)
  (* Make a polynomial monic.                                                *)
  (* ----------------------------------------------------------------------- *)

  let monic (pol,hist) =
    if pol = [] then (pol,hist) else
    let c',m' = hd pol in
    (map (fun (c,m) -> (c//c',m)) pol,
     Mmul((num_1 // c',map (K 0) m'),hist)) in

  (* ----------------------------------------------------------------------- *)
  (* The most popular heuristic is to order critical pairs by LCM monomial.  *)
  (* ----------------------------------------------------------------------- *)

  let forder ((c1,m1),_) ((c2,m2),_) = morder_lt m1 m2 in

  (* ----------------------------------------------------------------------- *)
  (* Stupid stuff forced on us by lack of equality test on num type.         *)
  (* ----------------------------------------------------------------------- *)

  let rec poly_lt p q =
    match (p,q) with
      p,[] -> false
    | [],q -> true
    | (c1,m1)::o1,(c2,m2)::o2 ->
          c1 </ c2 ||
          c1 =/ c2 && (m1 < m2 || m1 = m2 && poly_lt o1 o2) in

  let align ((p,hp),(q,hq)) =
    if poly_lt p q then ((p,hp),(q,hq)) else ((q,hq),(p,hp)) in

  let poly_eq p1 p2 =
    forall2 (fun (c1,m1) (c2,m2) -> c1 =/ c2 && m1 = m2) p1 p2 in

  let memx ((p1,h1),(p2,h2)) ppairs =
    not (exists (fun ((q1,_),(q2,_)) -> poly_eq p1 q1 && poly_eq p2 q2)
                ppairs) in

  (* ----------------------------------------------------------------------- *)
  (* Buchberger's second criterion.                                          *)
  (* ----------------------------------------------------------------------- *)

  let criterion2 basis (lcm,((p1,h1),(p2,h2))) opairs =
    exists (fun g -> not(poly_eq (fst g) p1) && not(poly_eq (fst g) p2) &&
                     can (mdiv lcm) (hd(fst g)) &&
                     not(memx (align(g,(p1,h1))) (map snd opairs)) &&
                     not(memx (align(g,(p2,h2))) (map snd opairs))) basis in

  (* ----------------------------------------------------------------------- *)
  (* Test for hitting constant polynomial.                                   *)
  (* ----------------------------------------------------------------------- *)

  let constant_poly p =
    length p = 1 && forall ((=) 0) (snd(hd p)) in

  (* ----------------------------------------------------------------------- *)
  (* Grobner basis algorithm.                                                *)
  (* ----------------------------------------------------------------------- *)

  let rec grobner_basis basis pairs =
    Format.print_string(string_of_int(length basis)^" basis elements and "^
                        string_of_int(length pairs)^" critical pairs");
    Format.print_newline();
    match pairs with
      [] -> basis
    | (l,(p1,p2))::opairs ->
          let (sp,hist as sph) = monic (reduce basis (spoly l p1 p2)) in
          if sp = [] || criterion2 basis (l,(p1,p2)) opairs
          then grobner_basis basis opairs else
          if constant_poly sp then grobner_basis (sph::basis) [] else
          let rawcps =
            map (fun p -> mlcm (hd(fst p)) (hd sp),align(p,sph)) basis in
          let newcps = filter
            (fun (l,(p,q)) -> not(orthogonal l (fst p) (fst q))) rawcps in
          grobner_basis (sph::basis)
                  (merge forder opairs (mergesort forder newcps)) in

  (* ----------------------------------------------------------------------- *)
  (* Interreduce initial polynomials.                                        *)
  (* ----------------------------------------------------------------------- *)

  let rec grobner_interreduce rpols ipols =
    match ipols with
      [] -> map monic (rev rpols)
    | p::ps -> let p' = reduce (rpols @ ps) p in
               if fst p' = [] then grobner_interreduce rpols ps
               else grobner_interreduce (p'::rpols) ps in

  (* ----------------------------------------------------------------------- *)
  (* Overall function.                                                       *)
  (* ----------------------------------------------------------------------- *)

  let grobner pols =
    let npols = map2 (fun p n -> p,Start n) pols (0--(length pols - 1)) in
    let phists = filter (fun (p,_) -> p <> []) npols in
    let bas = grobner_interreduce [] (map monic phists) in
    let prs0 = allpairs (fun x y -> x,y) bas bas in
    let prs1 = filter (fun ((x,_),(y,_)) -> poly_lt x y) prs0 in
    let prs2 = map (fun (p,q) -> mlcm (hd(fst p)) (hd(fst q)),(p,q)) prs1 in
    let prs3 =
      filter (fun (l,(p,q)) -> not(orthogonal l (fst p) (fst q))) prs2 in
    grobner_basis bas (mergesort forder prs3) in

  (* ----------------------------------------------------------------------- *)
  (* Get proof of contradiction from Grobner basis.                          *)
  (* ----------------------------------------------------------------------- *)

  let grobner_refute pols =
    let gb = grobner pols in
    snd(find (fun (p,h) -> length p = 1 && forall ((=)0) (snd(hd p))) gb) in

  (* ----------------------------------------------------------------------- *)
  (* Turn proof into a certificate as sum of multipliers.                    *)
  (*                                                                         *)
  (* In principle this is very inefficient: in a heavily shared proof it may *)
  (* make the same calculation many times. Could add a cache or something.   *)
  (* ----------------------------------------------------------------------- *)

  let rec resolve_proof vars prf =
    match prf with
      Start(-1) -> []
    | Start m -> [m,[num_1,map (K 0) vars]]
    | Mmul(pol,lin) ->
          let lis = resolve_proof vars lin in
          map (fun (n,p) -> n,grob_cmul pol p) lis
    | Add(lin1,lin2) ->
          let lis1 = resolve_proof vars lin1
          and lis2 = resolve_proof vars lin2 in
          let dom = setify(union (map fst lis1) (map fst lis2)) in
          map (fun n -> let a = try assoc n lis1 with Failure _ -> []
                        and b = try assoc n lis2 with Failure _ -> [] in
                        n,grob_add a b) dom in

  (* ----------------------------------------------------------------------- *)
  (* Run the procedure and produce Weak Nullstellensatz certificate.         *)
  (* ----------------------------------------------------------------------- *)

  let grobner_weak vars pols =
    let cert = resolve_proof vars (grobner_refute pols) in
    let l =
      itlist (itlist (lcm_num o denominator o fst) o snd) cert (num_1) in
    l,map (fun (i,p) -> i,map (fun (d,m) -> (l*/d,m)) p) cert in

  (* ----------------------------------------------------------------------- *)
  (* Prove polynomial is in ideal generated by others, using Grobner basis.  *)
  (* ----------------------------------------------------------------------- *)

  let grobner_ideal vars pols pol =
    let pol',h = reduce (grobner pols) (grob_neg pol,Start(-1)) in
    if pol' <> [] then failwith "grobner_ideal: not in the ideal" else
    resolve_proof vars h in

  (* ----------------------------------------------------------------------- *)
  (* Produce Strong Nullstellensatz certificate for a power of pol.          *)
  (* ----------------------------------------------------------------------- *)

  let grobner_strong vars pols pol =
    if pol = [] then 1,num_1,[] else
    let vars' = (concl TRUTH)::vars in
    let grob_z = [num_1,1::(map (fun x -> 0) vars)]
    and grob_1 = [num_1,(map (fun x -> 0) vars')]
    and augment = map (fun (c,m) -> (c,0::m)) in
    let pols' = map augment pols
    and pol' = augment pol in
    let allpols = (grob_sub (grob_mul grob_z pol') grob_1)::pols' in
    let l,cert = grobner_weak vars' allpols in
    let d = itlist (itlist (max o hd o snd) o snd) cert 0 in
    let transform_monomial (c,m) =
      grob_cmul (c,tl m) (grob_pow vars pol (d - hd m)) in
    let transform_polynomial q = itlist (grob_add o transform_monomial) q [] in
    let cert' = map (fun (c,q) -> c-1,transform_polynomial q)
                    (filter (fun (k,_) -> k <> 0) cert) in
    d,l,cert' in

  (* ----------------------------------------------------------------------- *)
  (* Overall parametrized universal procedure for (semi)rings.               *)
  (* We return an IDEAL_CONV and the actual ring prover.                     *)
  (* ----------------------------------------------------------------------- *)

  let pth_step = prove
   (`!(add:A->A->A) (mul:A->A->A) (n0:A).
          (!x. mul n0 x = n0) /\
          (!x y z. (add x y = add x z) <=> (y = z)) /\
          (!w x y z. (add (mul w y) (mul x z) = add (mul w z) (mul x y)) <=>
                     (w = x) \/ (y = z))
          ==> (!a b c d. ~(a = b) /\ ~(c = d) <=>
                         ~(add (mul a c) (mul b d) =
                           add (mul a d) (mul b c))) /\
              (!n a b c d. ~(n = n0)
                           ==> (a = b) /\ ~(c = d)
                               ==> ~(add a (mul n c) = add b (mul n d)))`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[GSYM DE_MORGAN_THM] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n0:A`; `n:A`; `d:A`; `c:A`]) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN ASM_SIMP_TAC[])
  and FINAL_RULE = MATCH_MP(TAUT `(p ==> F) ==> (~q = p) ==> q`)
  and false_tm = `F` in
  let rec refute_disj rfn tm =
    match tm with
      Comb(Comb(Const("\\/",_),l),r) ->
        DISJ_CASES (ASSUME tm) (refute_disj rfn l) (refute_disj rfn r)
    | _ -> rfn tm in
  fun (ring_dest_const,ring_mk_const,RING_EQ_CONV,
       ring_neg_tm,ring_add_tm,ring_sub_tm,
       ring_inv_tm,ring_mul_tm,ring_div_tm,ring_pow_tm,
       RING_INTEGRAL,RABINOWITSCH_THM,RING_NORMALIZE_CONV) ->
    let INITIAL_CONV =
      TOP_DEPTH_CONV BETA_CONV THENC
      PRESIMP_CONV THENC
      CONDS_ELIM_CONV THENC
      NNF_CONV THENC
      (if is_iff(snd(strip_forall(concl RABINOWITSCH_THM)))
       then GEN_REWRITE_CONV ONCE_DEPTH_CONV [RABINOWITSCH_THM]
       else ALL_CONV) THENC
      GEN_REWRITE_CONV REDEPTH_CONV
       [AND_FORALL_THM;
        LEFT_AND_FORALL_THM;
        RIGHT_AND_FORALL_THM;
        LEFT_OR_FORALL_THM;
        RIGHT_OR_FORALL_THM;
        OR_EXISTS_THM;
        LEFT_OR_EXISTS_THM;
        RIGHT_OR_EXISTS_THM;
        LEFT_AND_EXISTS_THM;
        RIGHT_AND_EXISTS_THM] in
    let ring_dest_neg t =
      let l,r = dest_comb t in
      if l = ring_neg_tm then r else failwith "ring_dest_neg"
    and ring_dest_inv t =
      let l,r = dest_comb t in
      if l = ring_inv_tm then r else failwith "ring_dest_inv"
    and ring_dest_add = dest_binop ring_add_tm
    and ring_mk_add = mk_binop ring_add_tm
    and ring_dest_sub = dest_binop ring_sub_tm
    and ring_dest_mul = dest_binop ring_mul_tm
    and ring_mk_mul = mk_binop ring_mul_tm
    and ring_dest_div = dest_binop ring_div_tm
    and ring_dest_pow = dest_binop ring_pow_tm
    and ring_mk_pow = mk_binop ring_pow_tm in
    let rec grobvars tm acc =
      if can ring_dest_const tm then acc
      else if can ring_dest_neg tm then grobvars (rand tm) acc
      else if can ring_dest_pow tm && is_numeral (rand tm)
           then grobvars (lhand tm) acc
      else if can ring_dest_add tm || can ring_dest_sub tm
           || can ring_dest_mul tm
           then grobvars (lhand tm) (grobvars (rand tm) acc)
      else if can ring_dest_inv tm then
           let gvs = grobvars (rand tm) [] in
           if gvs = [] then acc else tm::acc
      else if can ring_dest_div tm then
           let lvs = grobvars (lhand tm) acc
           and gvs = grobvars (rand tm) [] in
           if gvs = [] then lvs else tm::acc
      else tm::acc in
    let rec grobify_term vars tm =
      try if not(mem tm vars) then failwith "" else
          [num_1,map (fun i -> if i = tm then 1 else 0) vars]
      with Failure _ -> try
          let x = ring_dest_const tm in
          if x =/ num_0 then [] else [x,map (fun v -> 0) vars]
      with Failure _ -> try
          grob_neg(grobify_term vars (ring_dest_neg tm))
      with Failure _ -> try
          grob_inv(grobify_term vars (ring_dest_inv tm))
      with Failure _ -> try
          let l,r = ring_dest_add tm in
          grob_add (grobify_term vars l) (grobify_term vars r)
      with Failure _ -> try
          let l,r = ring_dest_sub tm in
          grob_sub (grobify_term vars l) (grobify_term vars r)
      with Failure _ -> try
          let l,r = ring_dest_mul tm in
          grob_mul (grobify_term vars l) (grobify_term vars r)
      with Failure _ -> try
          let l,r = ring_dest_div tm in
          grob_div (grobify_term vars l) (grobify_term vars r)
      with Failure _ -> try
          let l,r = ring_dest_pow tm in
          grob_pow vars (grobify_term vars l) (dest_small_numeral r)
      with Failure _ ->
            failwith "grobify_term: unknown or invalid term" in
    let grobify_equation vars tm =
      let l,r = dest_eq tm in
      grob_sub (grobify_term vars l) (grobify_term vars r) in
    let grobify_equations tm =
      let cjs = conjuncts tm in
      let rawvars =
        itlist (fun eq a -> grobvars (lhand eq) (grobvars (rand eq) a))
               cjs [] in
      let vars = sort (fun x y -> x < y) (setify rawvars) in
      vars,map (grobify_equation vars) cjs in
    let holify_polynomial =
      let holify_varpow (v,n) =
        if n = 1 then v else ring_mk_pow v (mk_small_numeral n) in
      let holify_monomial vars (c,m) =
        let xps = map holify_varpow
          (filter (fun (_,n) -> n <> 0) (zip vars m)) in
        end_itlist ring_mk_mul (ring_mk_const c :: xps) in
      let holify_polynomial vars p =
        if p = [] then ring_mk_const (num_0)
        else end_itlist ring_mk_add (map (holify_monomial vars) p) in
      holify_polynomial in
    let (pth_idom,pth_ine) = CONJ_PAIR(MATCH_MP pth_step RING_INTEGRAL) in
    let IDOM_RULE = CONV_RULE(REWR_CONV pth_idom) in
    let PROVE_NZ n = EQF_ELIM(RING_EQ_CONV
                (mk_eq(ring_mk_const n,ring_mk_const(num_0)))) in
    let NOT_EQ_01 = PROVE_NZ (num_1)
    and INE_RULE n = MATCH_MP(MATCH_MP pth_ine (PROVE_NZ n))
    and MK_ADD th1 th2 = MK_COMB(AP_TERM ring_add_tm th1,th2) in
    let execute_proof vars eths prf =
      let x,th1 = SPEC_VAR(CONJUNCT1(CONJUNCT2 RING_INTEGRAL)) in
      let y,th2 = SPEC_VAR th1 in
      let z,th3 = SPEC_VAR th2 in
      let SUB_EQ_RULE = GEN_REWRITE_RULE I
        [SYM(INST [mk_comb(ring_neg_tm,z),x] th3)] in
      let initpols = map (CONV_RULE(BINOP_CONV RING_NORMALIZE_CONV) o
                          SUB_EQ_RULE) eths in
      let ADD_RULE th1 th2 =
         CONV_RULE (BINOP_CONV RING_NORMALIZE_CONV)
                   (MK_COMB(AP_TERM ring_add_tm th1,th2))
      and MUL_RULE vars m th =
         CONV_RULE (BINOP_CONV RING_NORMALIZE_CONV)
                   (AP_TERM (mk_comb(ring_mul_tm,holify_polynomial vars [m]))
                            th) in
      let rec assoceq a l =
        match l with
         [] -> failwith "assoceq"
        | (x,y)::t -> if x==a then y else assoceq a t in
      let run_proof =
        if is_iff(snd(strip_forall(concl RABINOWITSCH_THM))) then
         (Format.print_string("Generating HOL version of proof");
          Format.print_newline();
          let execache = ref [] in
          let memoize prf x = (execache := (prf,x)::(!execache)); x in
          let rec run_proof vars prf =
            try assoceq prf (!execache) with Failure _ ->
            (match prf with
               Start m -> el m initpols
             | Add(p1,p2) ->
                memoize prf (ADD_RULE (run_proof vars p1) (run_proof vars p2))
             | Mmul(m,p2) ->
                memoize prf (MUL_RULE vars m (run_proof vars p2))) in
          fun vars prf ->
            let ans = run_proof vars prf in
            (execache := []; ans))
        else
         (Format.print_string("Generating HOL version of scaled proof");
          Format.print_newline();
          let km = map (fun x -> 0) vars in
          let execache = ref [] in
          let memoize prf x = (execache := (prf,x)::(!execache)); x in
          let rec run_scaled_proof vars prf =
            try assoceq prf (!execache) with Failure _ ->
            (match prf with
               Start m -> (num_1,el m initpols)
             | Add(p1,p2) ->
                    let d1,th1 = run_scaled_proof vars p1
                    and d2,th2 = run_scaled_proof vars p2 in
                    let d = lcm_num d1 d2 in
                    memoize prf
                     (d,ADD_RULE (MUL_RULE vars (d//d1,km) th1)
                                 (MUL_RULE vars (d//d2,km) th2))
             | Mmul((c,xs),p2) ->
                    let e = denominator c in
                    let d,th = run_scaled_proof vars p2 in
                    memoize prf ((d */ e),MUL_RULE vars (c */ e,xs) th)) in
          fun vars prf ->
            let _,ans = run_scaled_proof vars prf in
            (execache := []; ans)) in
      let th = run_proof vars prf in
      CONV_RULE RING_EQ_CONV th in
    let REFUTE tm =
      if tm = false_tm then ASSUME tm else
      let nths0,eths0 = partition (is_neg o concl) (CONJUNCTS(ASSUME tm)) in
      let nths = filter (is_eq o rand o concl) nths0
      and eths = filter (is_eq o concl) eths0 in
      if eths = [] then
        let th1 = end_itlist (fun th1 th2 -> IDOM_RULE(CONJ th1 th2)) nths in
        let th2 = CONV_RULE(RAND_CONV(BINOP_CONV RING_NORMALIZE_CONV)) th1 in
        let l,r = dest_eq(rand(concl th2)) in
        EQ_MP (EQF_INTRO th2) (REFL l)
      else if nths = [] && not(is_var ring_neg_tm) then
        let vars,pols = grobify_equations(list_mk_conj(map concl eths)) in
        execute_proof vars eths (grobner_refute pols)
      else
      let vars,l,cert,noteqth =
        if nths = [] then
          let vars,pols = grobify_equations(list_mk_conj(map concl eths)) in
          let l,cert = grobner_weak vars pols in
          vars,l,cert,NOT_EQ_01
        else
          let nth = end_itlist
           (fun th1 th2 -> IDOM_RULE(CONJ th1 th2)) nths in
          let vars,pol::pols =
           grobify_equations(list_mk_conj(rand(concl nth)::map concl eths)) in
          let deg,l,cert = grobner_strong vars pols pol in
          let th1 =
            CONV_RULE(RAND_CONV(BINOP_CONV RING_NORMALIZE_CONV)) nth in
          let th2 = funpow deg (IDOM_RULE o CONJ th1) NOT_EQ_01 in
          vars,l,cert,th2 in
      Format.print_string("Translating certificate to HOL inferences");
      Format.print_newline();
      let cert_pos = map
        (fun (i,p) -> i,filter (fun (c,m) -> c >/ num_0) p) cert
      and cert_neg = map
        (fun (i,p) -> i,map (fun (c,m) -> minus_num c,m)
                            (filter (fun (c,m) -> c </ num_0) p)) cert in
      let herts_pos =
        map (fun (i,p) -> i,holify_polynomial vars p) cert_pos
      and herts_neg =
        map (fun (i,p) -> i,holify_polynomial vars p) cert_neg in
      let thm_fn pols =
        if pols = [] then REFL(ring_mk_const num_0) else
        end_itlist MK_ADD
        (map (fun (i,p) -> AP_TERM(mk_comb(ring_mul_tm,p)) (el i eths))
             pols) in
      let th1 = thm_fn herts_pos and th2 = thm_fn herts_neg in
      let th3 = CONJ(MK_ADD (SYM th1) th2) noteqth in
      let th4 = CONV_RULE (RAND_CONV(BINOP_CONV RING_NORMALIZE_CONV))
                          (INE_RULE l th3) in
      let l,r = dest_eq(rand(concl th4)) in
      EQ_MP (EQF_INTRO th4) (REFL l) in
  let ring_ty = snd(dest_fun_ty(snd(dest_fun_ty(type_of ring_add_tm)))) in
  let RING tm =
    let avs = filter ((=) ring_ty o type_of) (frees tm) in
    let tm' = list_mk_forall(avs,tm) in
    let th1 = INITIAL_CONV(mk_neg tm') in
    let evs,bod = strip_exists(rand(concl th1)) in
    if is_forall bod then failwith "RING: non-universal formula" else
    let th1a = WEAK_DNF_CONV bod in
    let boda = rand(concl th1a) in
    let th2a = refute_disj REFUTE boda in
    let th2b = TRANS th1a (EQF_INTRO(NOT_INTRO(DISCH boda th2a))) in
    let th2 = UNDISCH(NOT_ELIM(EQF_ELIM th2b)) in
    let finbod,th3 =
      let rec CHOOSES evs (etm,th) =
        match evs with
          [] -> (etm,th)
        | ev::oevs ->
              let etm',th' = CHOOSES oevs (etm,th) in
              mk_exists(ev,etm'),CHOOSE (ev,ASSUME (mk_exists(ev,etm'))) th' in
      CHOOSES evs (bod,th2) in
    SPECL avs (MATCH_MP (FINAL_RULE (DISCH finbod th3)) th1)
  and ideal tms tm =
    let rawvars = itlist grobvars (tm::tms) [] in
    let vars = sort (fun x y -> x < y) (setify rawvars) in
    let pols = map (grobify_term vars) tms and pol = grobify_term vars tm in
    let cert = grobner_ideal vars pols pol in
    map (fun n -> let p = assocd n cert [] in holify_polynomial vars p)
        (0--(length pols-1)) in
  RING,ideal;;

(* ----------------------------------------------------------------------- *)
(* Separate out the cases.                                                 *)
(* ----------------------------------------------------------------------- *)

let RING parms = fst(RING_AND_IDEAL_CONV parms);;

let ideal_cofactors parms = snd(RING_AND_IDEAL_CONV parms);;

(* ------------------------------------------------------------------------- *)
(* Simplify a natural number assertion to eliminate conditionals, DIV, MOD,  *)
(* PRE, cutoff subtraction, EVEN and ODD. Try to do it in a way that makes   *)
(* new quantifiers universal. At the moment we don't split "<=>" which would *)
(* make this quantifier selection work there too; better to do NNF first if  *)
(* you care. This also applies to EVEN and ODD.                              *)
(* ------------------------------------------------------------------------- *)

let NUM_SIMPLIFY_CONV =
  let pre_tm = `PRE`
  and div_tm = `(DIV):num->num->num`
  and mod_tm = `(MOD):num->num->num`
  and p_tm = `P:num->bool` and n_tm = `n:num` and m_tm = `m:num`
  and q_tm = `P:num->num->bool` and a_tm = `a:num` and b_tm = `b:num` in
  let is_pre tm = is_comb tm && rator tm = pre_tm
  and is_sub = is_binop `(-):num->num->num`
  and is_divmod =
    let is_div = is_binop div_tm and is_mod = is_binop mod_tm in
    fun tm -> is_div tm || is_mod tm
  and contains_quantifier =
    can (find_term (fun t -> is_forall t || is_exists t || is_uexists t))
  and BETA2_CONV = RATOR_CONV BETA_CONV THENC BETA_CONV
  and PRE_ELIM_THM'' = CONV_RULE (RAND_CONV NNF_CONV) PRE_ELIM_THM
  and SUB_ELIM_THM'' = CONV_RULE (RAND_CONV NNF_CONV) SUB_ELIM_THM
  and DIVMOD_ELIM_THM'' = CONV_RULE (RAND_CONV NNF_CONV) DIVMOD_ELIM_THM
  and pth_evenodd = prove
   (`(EVEN(x) <=> (!y. ~(x = SUC(2 * y)))) /\
     (ODD(x) <=> (!y. ~(x = 2 * y))) /\
     (~EVEN(x) <=> (!y. ~(x = 2 * y))) /\
     (~ODD(x) <=> (!y. ~(x = SUC(2 * y))))`,
    REWRITE_TAC[GSYM NOT_EXISTS_THM; GSYM EVEN_EXISTS; GSYM ODD_EXISTS] THEN
    REWRITE_TAC[NOT_EVEN; NOT_ODD]) in
  let rec NUM_MULTIPLY_CONV pos tm =
    if is_forall tm || is_exists tm || is_uexists tm then
       BINDER_CONV (NUM_MULTIPLY_CONV pos) tm
    else if is_imp tm && contains_quantifier tm then
        COMB2_CONV (RAND_CONV(NUM_MULTIPLY_CONV(not pos)))
                   (NUM_MULTIPLY_CONV pos) tm
    else if (is_conj tm || is_disj tm || is_iff tm) &&
            contains_quantifier tm
         then BINOP_CONV (NUM_MULTIPLY_CONV pos) tm
    else if is_neg tm && not pos && contains_quantifier tm then
       RAND_CONV (NUM_MULTIPLY_CONV (not pos)) tm
    else
       try let t = find_term (fun t -> is_pre t && free_in t tm) tm in
           let ty = type_of t in
           let v = genvar ty in
           let p = mk_abs(v,subst [v,t] tm) in
           let th0 = if pos then PRE_ELIM_THM'' else PRE_ELIM_THM' in
           let th1 = INST [p,p_tm; rand t,n_tm] th0 in
           let th2 = CONV_RULE(COMB2_CONV (RAND_CONV BETA_CONV)
                      (BINDER_CONV(RAND_CONV BETA_CONV))) th1 in
           CONV_RULE(RAND_CONV (NUM_MULTIPLY_CONV pos)) th2
       with Failure _ -> try
           let t = find_term (fun t -> is_sub t && free_in t tm) tm in
           let ty = type_of t in
           let v = genvar ty in
           let p = mk_abs(v,subst [v,t] tm) in
           let th0 = if pos then SUB_ELIM_THM'' else SUB_ELIM_THM' in
           let th1 = INST [p,p_tm; lhand t,a_tm; rand t,b_tm] th0 in
           let th2 = CONV_RULE(COMB2_CONV (RAND_CONV BETA_CONV)
                      (BINDER_CONV(RAND_CONV BETA_CONV))) th1 in
           CONV_RULE(RAND_CONV (NUM_MULTIPLY_CONV pos)) th2
       with Failure _ -> try
           let t = find_term (fun t -> is_divmod t && free_in t tm) tm in
           let x = lhand t and y = rand t in
           let dtm = mk_comb(mk_comb(div_tm,x),y)
           and mtm = mk_comb(mk_comb(mod_tm,x),y) in
           let vd = genvar(type_of dtm)
           and vm = genvar(type_of mtm) in
           let p = list_mk_abs([vd;vm],subst[vd,dtm; vm,mtm] tm) in
           let th0 = if pos then DIVMOD_ELIM_THM'' else DIVMOD_ELIM_THM' in
           let th1 = INST [p,q_tm; x,m_tm; y,n_tm] th0 in
           let th2 = CONV_RULE(COMB2_CONV(RAND_CONV BETA2_CONV)
                (funpow 2 BINDER_CONV(RAND_CONV BETA2_CONV))) th1 in
           CONV_RULE(RAND_CONV (NUM_MULTIPLY_CONV pos)) th2
       with Failure _ -> REFL tm in
  NUM_REDUCE_CONV THENC
  CONDS_CELIM_CONV THENC
  NNF_CONV THENC
  NUM_MULTIPLY_CONV true THENC
  NUM_REDUCE_CONV THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [pth_evenodd];;

(* ----------------------------------------------------------------------- *)
(* Natural number version of ring procedure with this normalization.       *)
(* ----------------------------------------------------------------------- *)

let NUM_RING =
  let NUM_INTEGRAL_LEMMA = prove
   (`(w = x + d) /\ (y = z + e)
     ==> ((w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))`,
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
    ONCE_REWRITE_TAC[AC ADD_AC
     `a + b + c + d + e = a + c + e + b + d`] THEN
    REWRITE_TAC[EQ_ADD_LCANCEL; EQ_ADD_LCANCEL_0; MULT_EQ_0]) in
  let NUM_INTEGRAL = prove
   (`(!x. 0 * x = 0) /\
     (!x y z. (x + y = x + z) <=> (y = z)) /\
     (!w x y z. (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))`,
    REWRITE_TAC[MULT_CLAUSES; EQ_ADD_LCANCEL] THEN
    REPEAT GEN_TAC THEN
    DISJ_CASES_TAC (SPECL [`w:num`; `x:num`] LE_CASES) THEN
    DISJ_CASES_TAC (SPECL [`y:num`; `z:num`] LE_CASES) THEN
    REPEAT(FIRST_X_ASSUM
     (CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS])) THEN
    ASM_MESON_TAC[NUM_INTEGRAL_LEMMA; ADD_SYM; MULT_SYM]) in
  let rawring =
    RING(dest_numeral,mk_numeral,NUM_EQ_CONV,
         genvar bool_ty,`(+):num->num->num`,genvar bool_ty,
         genvar bool_ty,`(*):num->num->num`,genvar bool_ty,
         `(EXP):num->num->num`,
         NUM_INTEGRAL,TRUTH,NUM_NORMALIZE_CONV) in
  let initconv = NUM_SIMPLIFY_CONV THENC GEN_REWRITE_CONV DEPTH_CONV [ADD1]
  and t_tm = `T` in
  fun tm -> let th = initconv tm in
            if rand(concl th) = t_tm then th
            else EQ_MP (SYM th) (rawring(rand(concl th)));;
