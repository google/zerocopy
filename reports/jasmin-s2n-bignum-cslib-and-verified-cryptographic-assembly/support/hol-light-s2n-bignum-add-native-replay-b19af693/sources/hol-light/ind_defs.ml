(* ========================================================================= *)
(* Mutually inductively defined relations.                                   *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "theorems.ml";;

(* ------------------------------------------------------------------------- *)
(* Strip off exactly n arguments from combination.                           *)
(* ------------------------------------------------------------------------- *)

let strip_ncomb =
  let rec strip(n,tm,acc) =
    if n < 1 then tm,acc else
    let l,r = dest_comb tm in
    strip(n - 1,l,r::acc) in
  fun n tm -> strip(n,tm,[]);;

(* ------------------------------------------------------------------------- *)
(* Expand lambda-term function definition with its arguments.                *)
(* ------------------------------------------------------------------------- *)

let RIGHT_BETAS =
  rev_itlist (fun a -> CONV_RULE (RAND_CONV BETA_CONV) o C AP_THM a);;

(* ------------------------------------------------------------------------- *)
(*      A, x = t |- P[x]                                                     *)
(*     ------------------ EXISTS_EQUATION                                    *)
(*        A |- ?x. P[x]                                                      *)
(* ------------------------------------------------------------------------- *)

let EXISTS_EQUATION =
  let pth = prove
   (`!P t. (!x:A. (x = t) ==> P x) ==> (?) P`,
    REWRITE_TAC[EXISTS_DEF] THEN BETA_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `t:A` THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REFL_TAC) in
  fun tm th ->
    let l,r = dest_eq tm in
    let P = mk_abs(l,concl th) in
    let th1 = BETA_CONV(mk_comb(P,l)) in
    let th2 = ISPECL [P; r] pth in
    let th3 = EQ_MP (SYM th1) th in
    let th4 = GEN l (DISCH tm th3) in
    MP th2 th4;;

(* ========================================================================= *)
(* Part 1: The main part of the inductive definitions package.               *)
(* This proves that a certain definition yields the requires theorems.       *)
(* ========================================================================= *)

let derive_nonschematic_inductive_relations =
  let getconcl tm =
    let bod = repeat (snd o dest_forall) tm in
    try snd(dest_imp bod) with Failure _ -> bod
  and CONJ_ACI_RULE = AC CONJ_ACI
  and SIMPLE_DISJ_PAIR th =
    let l,r = dest_disj(hd(hyp th)) in
    PROVE_HYP (DISJ1 (ASSUME l) r) th,PROVE_HYP (DISJ2 l (ASSUME r)) th
  and HALF_BETA_EXPAND args th = GENL args (RIGHT_BETAS args th) in
  let AND_IMPS_CONV tm =
    let ths = CONJUNCTS(ASSUME tm) in
    let avs = fst(strip_forall(concl(hd ths))) in
    let thl = map (DISCH tm o UNDISCH o SPEC_ALL) ths in
    let th1 = end_itlist SIMPLE_DISJ_CASES thl in
    let tm1 = hd(hyp th1) in
    let th2 = GENL avs (DISCH tm1 (UNDISCH th1)) in
    let tm2 = concl th2 in
    let th3 = DISCH tm2 (UNDISCH (SPEC_ALL (ASSUME tm2))) in
    let thts,tht =  nsplit SIMPLE_DISJ_PAIR (tl ths) th3 in
    let proc_fn th =
      let t = hd(hyp th) in GENL avs (DISCH t (UNDISCH th)) in
    let th4 = itlist (CONJ o proc_fn) thts (proc_fn tht) in
    IMP_ANTISYM_RULE (DISCH_ALL th2) (DISCH_ALL th4) in
  let t_tm = `T` in
  let calculate_simp_sequence =
    let rec getequs(avs,plis) =
      if plis = [] then [] else
      let h::t = plis in
      let r = snd h in
      if mem r avs then
        h::(getequs(avs,filter ((<>) r o snd) t))
      else
        getequs(avs,t) in
    fun avs plis ->
      let oks = getequs(avs,plis) in
      oks,subtract plis oks
  and FORALL_IMPS_CONV tm =
    let avs,bod = strip_forall tm in
    let th1 = DISCH tm (UNDISCH(SPEC_ALL(ASSUME tm))) in
    let th2 = itlist SIMPLE_CHOOSE avs th1 in
    let tm2 = hd(hyp th2) in
    let th3 = DISCH tm2 (UNDISCH th2) in
    let th4 = ASSUME (concl th3) in
    let ant = lhand bod in
    let th5 = itlist SIMPLE_EXISTS avs (ASSUME ant) in
    let th6 = GENL avs (DISCH ant (MP th4 th5)) in
    IMP_ANTISYM_RULE (DISCH_ALL th3) (DISCH_ALL th6) in
  let canonicalize_clause cls args =
    let avs,bimp = strip_forall cls in
    let ant,con = try dest_imp bimp with Failure _ -> t_tm,bimp in
    let rel,xargs = strip_comb con in
    let plis = zip args xargs in
    let yes,no = calculate_simp_sequence avs plis in
    let nvs = filter (not o C mem (map snd yes)) avs in
    let eth =
      if is_imp bimp then
        let atm = itlist (curry mk_conj o mk_eq) (yes@no) ant in
        let ths,tth = nsplit CONJ_PAIR plis (ASSUME atm) in
        let thl = map (fun t -> find (fun th -> lhs(concl th) = t) ths) args in
        let th0 = MP (SPECL avs (ASSUME cls)) tth in
        let th1 = rev_itlist (C (curry MK_COMB)) thl (REFL rel) in
        let th2 = EQ_MP (SYM th1) th0 in
        let th3 = INST yes (DISCH atm th2) in
        let tm4 = funpow (length yes) rand (lhand(concl th3)) in
        let th4 = itlist (CONJ o REFL o fst) yes (ASSUME tm4) in
        let th5 = GENL args (GENL nvs (DISCH tm4 (MP th3 th4))) in
        let th6 = SPECL nvs (SPECL (map snd plis) (ASSUME (concl th5))) in
        let th7 = itlist (CONJ o REFL o snd) no (ASSUME ant) in
        let th8 = GENL avs (DISCH ant (MP th6 th7)) in
        IMP_ANTISYM_RULE (DISCH_ALL th5) (DISCH_ALL th8)
      else
        let atm = list_mk_conj(map mk_eq (yes@no)) in
        let ths = CONJUNCTS (ASSUME atm) in
        let thl = map (fun t -> find (fun th -> lhs(concl th) = t) ths) args in
        let th0 = SPECL avs (ASSUME cls) in
        let th1 = rev_itlist (C (curry MK_COMB)) thl (REFL rel) in
        let th2 = EQ_MP (SYM th1) th0 in
        let th3 = INST yes (DISCH atm th2) in
        let tm4 = funpow (length yes) rand (lhand(concl th3)) in
        let th4 = itlist (CONJ o REFL o fst) yes (ASSUME tm4) in
        let th5 = GENL args (GENL nvs (DISCH tm4 (MP th3 th4))) in
        let th6 = SPECL nvs (SPECL (map snd plis) (ASSUME (concl th5))) in
        let th7 = end_itlist CONJ (map (REFL o snd) no) in
        let th8 = GENL avs (MP th6 th7) in
        IMP_ANTISYM_RULE (DISCH_ALL th5) (DISCH_ALL th8) in
    let ftm = funpow (length args) (body o rand) (rand(concl eth)) in
    TRANS eth (itlist MK_FORALL args (FORALL_IMPS_CONV ftm)) in
  let canonicalize_clauses clauses =
    let concls = map getconcl clauses in
    let uncs = map strip_comb concls in
    let rels = itlist (insert o fst) uncs [] in
    let xargs = map (C assoc uncs) rels in
    let closed = list_mk_conj clauses in
    let avoids = variables closed in
    let flargs =
      make_args "a" avoids (map type_of (end_itlist (@) xargs)) in
    let zargs = zip rels (shareout xargs flargs) in
    let cargs = map (fun (r,a) -> assoc r zargs) uncs in
    let cthms = map2 canonicalize_clause clauses cargs in
    let pclauses = map (rand o concl) cthms in
    let collectclauses tm =
      mapfilter (fun t -> if fst t = tm then snd t else fail())
                (zip (map fst uncs) pclauses) in
    let clausell = map collectclauses rels in
    let cclausel = map list_mk_conj clausell in
    let cclauses = list_mk_conj cclausel
    and oclauses = list_mk_conj pclauses in
    let eth = CONJ_ACI_RULE(mk_eq(oclauses,cclauses)) in
    let pth = TRANS (end_itlist MK_CONJ cthms) eth in
    TRANS pth (end_itlist MK_CONJ (map AND_IMPS_CONV cclausel))
  and derive_canon_inductive_relations clauses =
    let closed = list_mk_conj clauses in
    let clauses = conjuncts closed in
    let vargs,bodies = unzip(map strip_forall clauses) in
    let ants,concs = unzip(map dest_imp bodies) in
    let rels = map (repeat rator) concs in
    let avoids = variables closed in
    let rels' = variants avoids rels in
    let crels = zip rels' rels in
    let prime_fn = subst crels in
    let closed' = prime_fn closed in
    let mk_def arg con =
      mk_eq(repeat rator con,
        list_mk_abs(arg,list_mk_forall(rels',mk_imp(closed',prime_fn con)))) in
    let deftms = map2 mk_def vargs concs in
    let defthms = map2 HALF_BETA_EXPAND vargs (map ASSUME deftms) in
    let mk_ind args th =
      let th1 = fst(EQ_IMP_RULE(SPEC_ALL th)) in
      let ant = lhand(concl th1) in
      let th2 = SPECL rels' (UNDISCH th1) in
      GENL args (DISCH ant (UNDISCH th2)) in
    let indthms = map2 mk_ind vargs defthms in
    let indthmr = end_itlist CONJ indthms in
    let indthm = GENL rels' (DISCH closed' indthmr) in
    let mconcs = map2 (fun a t -> list_mk_forall(a,mk_imp(t,prime_fn t)))
      vargs ants in
    let monotm = mk_imp(concl indthmr,list_mk_conj mconcs) in
    let monothm = ASSUME(list_mk_forall(rels,list_mk_forall(rels',monotm))) in
    let closthm = ASSUME closed' in
    let monothms = CONJUNCTS
      (MP (SPEC_ALL monothm) (MP (SPECL rels' indthm) closthm)) in
    let closthms = CONJUNCTS closthm in
    let prove_rule mth (cth,dth) =
      let avs,bod = strip_forall(concl mth) in
      let th1 = IMP_TRANS (SPECL avs mth) (SPECL avs cth) in
      let th2 = GENL rels' (DISCH closed' (UNDISCH th1)) in
      let th3 = EQ_MP (SYM (SPECL avs dth)) th2 in
      GENL avs (DISCH (lhand bod) th3) in
    let rulethms = map2 prove_rule monothms (zip closthms defthms) in
    let rulethm = end_itlist CONJ rulethms in
    let dtms = map2 (curry list_mk_abs) vargs ants in
    let double_fn = subst (zip dtms rels) in
    let mk_unbetas tm dtm =
      let avs,bod = strip_forall tm in
      let il,r = dest_comb bod in
      let i,l = dest_comb il in
      let bth = RIGHT_BETAS avs (REFL dtm) in
      let munb = AP_THM (AP_TERM i bth) r in
      let iunb = AP_TERM (mk_comb(i,double_fn l)) bth in
      let junb = AP_TERM (mk_comb(i,r)) bth in
      let quantify = itlist MK_FORALL avs in
      (quantify munb,(quantify iunb,quantify junb)) in
    let unths = map2 mk_unbetas clauses dtms in
    let irthm = EQ_MP (SYM(end_itlist MK_CONJ (map fst unths))) rulethm in
    let mrthm = MP (SPECL rels (SPECL dtms monothm)) irthm in
    let imrth = EQ_MP (SYM(end_itlist MK_CONJ (map (fst o snd) unths))) mrthm in
    let ifthm = MP (SPECL dtms indthm) imrth in
    let fthm = EQ_MP (end_itlist MK_CONJ (map (snd o snd) unths)) ifthm in
    let mk_case th1 th2 =
      let avs = fst(strip_forall(concl th1)) in
      GENL avs (IMP_ANTISYM_RULE (SPEC_ALL th1) (SPEC_ALL th2)) in
    let casethm = end_itlist CONJ
      (map2 mk_case (CONJUNCTS fthm) (CONJUNCTS rulethm)) in
    CONJ rulethm (CONJ indthm casethm) in
  fun tm ->
    let clauses = conjuncts tm in
    let canonthm = canonicalize_clauses clauses in
    let canonthm' = SYM canonthm in
    let pclosed = rand(concl canonthm) in
    let pclauses = conjuncts pclosed in
    let rawthm = derive_canon_inductive_relations pclauses in
    let rulethm,otherthms = CONJ_PAIR rawthm in
    let indthm,casethm = CONJ_PAIR otherthms in
    let rulethm' = EQ_MP canonthm' rulethm
    and indthm' = CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV canonthm')) indthm in
    CONJ rulethm' (CONJ indthm' casethm);;

(* ========================================================================= *)
(* Part 2: Tactic-integrated tools for proving monotonicity automatically.   *)
(* ========================================================================= *)

let monotonicity_theorems = ref
 [MONO_AND; MONO_OR; MONO_IMP; MONO_NOT; MONO_EXISTS; MONO_FORALL];;

(* ------------------------------------------------------------------------- *)
(* Attempt to backchain through the monotonicity theorems.                   *)
(* ------------------------------------------------------------------------- *)

let MONO_TAC =
  let imp = `(==>)` and IMP_REFL = ITAUT `!p. p ==> p` in
  let BACKCHAIN_TAC th =
    let match_fn = PART_MATCH (snd o dest_imp) th in
    fun (asl,w) ->
      let th1 = match_fn w in
      let ant,con = dest_imp(concl th1) in
      null_meta,[asl,ant],fun i [t] -> MATCH_MP (INSTANTIATE i th1) t
  and MONO_ABS_TAC (asl,w) =
    let ant,con = dest_imp w in
    let vars = snd(strip_comb con) in
    let rnum = length vars - 1 in
    let hd1,args1 = strip_ncomb rnum ant
    and hd2,args2 = strip_ncomb rnum con in
    let th1 = rev_itlist (C AP_THM) args1 (BETA_CONV hd1)
    and th2 = rev_itlist (C AP_THM) args1 (BETA_CONV hd2) in
    let th3 = MK_COMB(AP_TERM imp th1,th2) in
    CONV_TAC(REWR_CONV th3) (asl,w)
  and APPLY_MONOTAC tacs (asl,w) =
    let a,c = dest_imp w in
    if aconv a c then ACCEPT_TAC (SPEC a IMP_REFL) (asl,w) else
    let cn = try fst(dest_const(repeat rator c)) with Failure _ -> "" in
    tryfind (fun (k,t) -> if k = cn then t (asl,w) else fail()) tacs in
  fun gl ->
    let tacs = itlist
      (fun th l -> let ft = repeat rator (funpow 2 rand (concl th)) in
                   let c = try fst(dest_const ft) with Failure _ -> "" in
                   (c,BACKCHAIN_TAC th THEN REPEAT CONJ_TAC)::l)
      (!monotonicity_theorems) ["",MONO_ABS_TAC] in
    let MONO_STEP_TAC = REPEAT GEN_TAC THEN APPLY_MONOTAC tacs in
    (REPEAT MONO_STEP_TAC THEN ASM_REWRITE_TAC[]) gl;;

(* ------------------------------------------------------------------------- *)
(* Attempt to dispose of the non-equational assumption(s) of a theorem.      *)
(* ------------------------------------------------------------------------- *)

let prove_monotonicity_hyps =
  let tac = REPEAT GEN_TAC THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    REPEAT CONJ_TAC THEN MONO_TAC in
  let prove_mth t = prove(t,tac) in
  fun th ->
    let mths = mapfilter prove_mth (filter (not o is_eq) (hyp th)) in
    itlist PROVE_HYP mths th;;

(* ========================================================================= *)
(* Part 3: The final user wrapper, with schematic variables added.           *)
(* ========================================================================= *)

let the_inductive_definitions = ref [];;

let prove_inductive_relations_exist,new_inductive_definition =
  let rec pare_comb qvs tm =
    if intersect (frees tm) qvs = [] && forall is_var (snd(strip_comb tm))
    then tm
    else pare_comb qvs (rator tm) in
  let generalize_schematic_variables gflag vs =
    let generalize_def tm th =
      let l,r = dest_eq tm in
      let lname,lty = dest_var l in
      let l' = mk_var(lname,itlist (mk_fun_ty o type_of) vs lty) in
      let r' = list_mk_abs(vs,r) in
      let tm' = mk_eq(l',r') in
      let th0 = RIGHT_BETAS vs (ASSUME tm') in
      let th1 = INST [lhs(concl th0),l] (DISCH tm th) in
      MP th1 th0 in
    fun th ->
      let defs,others = partition is_eq (hyp th) in
      let th1 = itlist generalize_def defs th in
      if gflag then
        let others' = map (fun t -> let fvs = frees t in
                                    SPECL fvs (ASSUME (list_mk_forall(fvs,t))))
                          others in
        GENL vs (itlist PROVE_HYP others' th1)
      else th1
  and derive_existence th =
    let defs = filter is_eq (hyp th) in
    itlist EXISTS_EQUATION defs th
  and make_definitions th =
    let defs = filter is_eq (hyp th) in
    let dths = map new_definition defs in
    let insts = zip (map (lhs o concl) dths) (map lhs defs) in
    rev_itlist (C MP) dths (INST insts (itlist DISCH defs th))
  and unschematize_clauses clauses =
    let schem = map (fun cls -> let avs,bod = strip_forall cls in
                  pare_comb avs (try snd(dest_imp bod) with Failure _ -> bod))
                            clauses in
      let schems = setify schem in
      if is_var(hd schem) then (clauses,[]) else
      if not (length(setify (map (snd o strip_comb) schems)) = 1)
      then failwith "Schematic variables not used consistently" else
      let avoids = variables (list_mk_conj clauses) in
      let hack_fn tm = mk_var(fst(dest_var(repeat rator tm)),type_of tm) in
      let grels = variants avoids (map hack_fn schems) in
      let crels = zip grels schems in
      let clauses' = map (subst crels) clauses in
      clauses',snd(strip_comb(hd schems)) in
  let find_redefinition tm (rth,ith,cth as trip):((thm*thm*thm)*thm) =
    (trip,PART_MATCH I rth tm) in
  let prove_inductive_properties tm =
    let clauses = conjuncts tm in
    let clauses',fvs = unschematize_clauses clauses in
    let th = derive_nonschematic_inductive_relations (list_mk_conj clauses') in
    fvs,prove_monotonicity_hyps th in
  let prove_inductive_relations_exist tm =
    let fvs,th1 = prove_inductive_properties tm in
    let th2 = generalize_schematic_variables true fvs th1 in
    derive_existence th2
  and new_inductive_definition tm =
    try let tm' = snd(strip_forall tm) in
        let th,_ = tryfind (find_redefinition tm')
          (!the_inductive_definitions) in
        warn true "Benign redefinition of inductive predicate";th
    with Failure _ ->
    let fvs,th1 = prove_inductive_properties tm in
    let th2 = generalize_schematic_variables true fvs th1 in
    let th3 = make_definitions th2 in
    let avs = fst(strip_forall(concl th3)) in
    let r,ic = CONJ_PAIR(SPECL avs th3) in
    let i,c = CONJ_PAIR ic in
    let thtr = GENL avs r,GENL avs i,GENL avs c in
    the_inductive_definitions := thtr::(!the_inductive_definitions);
    thtr in
  prove_inductive_relations_exist,new_inductive_definition;;

(* ------------------------------------------------------------------------- *)
(* Derivation of "strong induction".                                         *)
(* ------------------------------------------------------------------------- *)

let derive_strong_induction =
  let dest_ibod tm =
    let avs,ibod = strip_forall tm in
    let n = length avs in
    let prator = funpow n rator in
    let ant,con = dest_imp ibod in
    n,(prator ant,prator con) in
  let rec prove_triv tm =
    if is_conj tm then CONJ (prove_triv(lhand tm)) (prove_triv(rand tm)) else
    let avs,bod = strip_forall tm in
    let a,c = dest_imp bod in
    let ths = CONJUNCTS(ASSUME a) in
    let th = find (aconv c o concl) ths in
    GENL avs (DISCH a th) in
  let rec weaken_triv th =
    if is_conj(concl th)
    then CONJ (weaken_triv(CONJUNCT1 th)) (weaken_triv(CONJUNCT2 th)) else
    let avs,bod = strip_forall(concl th) in
    let th1 = SPECL avs th in
    let a = fst(dest_imp(concl th1)) in
    GENL avs (DISCH a (CONJUNCT2 (UNDISCH th1))) in
  let MATCH_IMPS = MATCH_MP MONO_AND in
  fun (rth,ith) ->
    let ovs,ibod = strip_forall(concl ith) in
    let iant,icon = dest_imp ibod in
    let ns,prrs = unzip (map dest_ibod (conjuncts icon)) in
    let rs,ps = unzip prrs in
    let gs = variants (variables ibod) ps in
    let svs,tvs = chop_list (length ovs - length ns) ovs in
    let sth = SPECL svs rth and jth = SPECL svs ith in
    let gimps = subst (zip gs rs) icon in
    let prs = map2 (fun n (r,p) ->
      let tys,ty = nsplit dest_fun_ty (1--n) (type_of r) in
      let gvs = map genvar tys in
      list_mk_abs(gvs,mk_conj(list_mk_comb(r,gvs),list_mk_comb(p,gvs))))
     ns prrs in
    let modify_rule rcl itm =
      let avs,bod = strip_forall itm in
      if is_imp bod then
        let a,c = dest_imp bod in
        let mgoal = mk_imp(gimps,mk_imp(vsubst(zip gs ps) a,a)) in
        let mth = ASSUME(list_mk_forall(gs@ps@avs,mgoal)) in
        let ith_r = BETA_RULE(SPECL (prs @ rs @ avs) mth) in
        let jth_r = MP ith_r (prove_triv(lhand(concl ith_r))) in
        let t = lhand(concl jth_r) in
        let kth_r = UNDISCH jth_r in
        let ntm = list_mk_forall(avs,mk_imp(t,c)) in
        let lth_r = MP(SPECL avs rcl) kth_r
        and lth_p = UNDISCH(SPECL avs (ASSUME ntm)) in
        DISCH ntm (GENL avs (DISCH t (CONJ lth_r lth_p)))
      else
        DISCH itm (GENL avs (CONJ (SPECL avs rcl) (SPECL avs (ASSUME itm)))) in
    let mimps = map2 modify_rule (CONJUNCTS sth) (conjuncts iant) in
    let th1 = end_itlist (fun th th' -> MATCH_IMPS(CONJ th th')) mimps in
    let th2 = BETA_RULE(SPECL prs jth) in
    let th3 = IMP_TRANS th1 th2 in
    let nasm = lhand(concl th3) in
    let th4 = GENL ps (DISCH nasm (weaken_triv(UNDISCH th3))) in
    GENL svs (prove_monotonicity_hyps th4);;
