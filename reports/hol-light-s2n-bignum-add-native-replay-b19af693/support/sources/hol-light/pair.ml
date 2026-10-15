(* ========================================================================= *)
(* Syntax sugaring; theory of pairing, with a bit of support.                *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                 (c) Copyright, Marco Maggesi 2015                         *)
(* ========================================================================= *)

needs "impconv.ml";;

(* ------------------------------------------------------------------------- *)
(* Constants implementing (or at least tagging) syntactic sugar.             *)
(* ------------------------------------------------------------------------- *)

let LET_DEF = new_definition
 `LET (f:A->B) x = f x`;;

let LET_END_DEF = new_definition
 `LET_END (t:A) = t`;;

let GABS_DEF = new_definition
 `GABS (P:A->bool) = (@) P`;;

let GEQ_DEF = new_definition
 `GEQ a b = (a:A = b)`;;

let _SEQPATTERN = new_definition
 `_SEQPATTERN = \(r:A->B->bool) s x. if ?y. r x y then r x else s x`;;

let _UNGUARDED_PATTERN = new_definition
 `_UNGUARDED_PATTERN = \p r. p /\ r`;;

let _GUARDED_PATTERN = new_definition
 `_GUARDED_PATTERN = \p g r. p /\ g /\ r`;;

let _MATCH = new_definition
 `_MATCH =  \e (r:A->B->bool). if (?!) (r e) then (@) (r e) else @z. F`;;

let _FUNCTION = new_definition
 `_FUNCTION = \(r:A->B->bool) x. if (?!) (r x) then (@) (r x) else @z. F`;;

(* ------------------------------------------------------------------------- *)
(* Pair type.                                                                *)
(* ------------------------------------------------------------------------- *)

let mk_pair_def = new_definition
  `mk_pair (x:A) (y:B) = \a b. (a = x) /\ (b = y)`;;

let PAIR_EXISTS_THM = prove
 (`?x. ?(a:A) (b:B). x = mk_pair a b`,
  MESON_TAC[]);;

let prod_tybij = new_type_definition
  "prod" ("ABS_prod","REP_prod") PAIR_EXISTS_THM;;

let REP_ABS_PAIR = prove
 (`!(x:A) (y:B). REP_prod (ABS_prod (mk_pair x y)) = mk_pair x y`,
  MESON_TAC[prod_tybij]);;

parse_as_infix (",",(14,"right"));;

let COMMA_DEF = new_definition
 `(x:A),(y:B) = ABS_prod(mk_pair x y)`;;

let FST_DEF = new_definition
 `FST (p:A#B) = @x. ?y. p = x,y`;;

let SND_DEF = new_definition
 `SND (p:A#B) = @y. ?x. p = x,y`;;

let PAIR_EQ = prove
 (`!(x:A) (y:B) a b. (x,y = a,b) <=> (x = a) /\ (y = b)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[COMMA_DEF] THEN
    DISCH_THEN(MP_TAC o AP_TERM `REP_prod:A#B->A->B->bool`) THEN
    REWRITE_TAC[REP_ABS_PAIR] THEN REWRITE_TAC[mk_pair_def; FUN_EQ_THM];
    ALL_TAC] THEN
  MESON_TAC[]);;

let PAIR_SURJECTIVE = prove
 (`!p:A#B. ?x y. p = x,y`,
  GEN_TAC THEN REWRITE_TAC[COMMA_DEF] THEN
  MP_TAC(SPEC `REP_prod p :A->B->bool` (CONJUNCT2 prod_tybij)) THEN
  REWRITE_TAC[CONJUNCT1 prod_tybij] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:B` MP_TAC)) THEN
  DISCH_THEN(MP_TAC o AP_TERM `ABS_prod:(A->B->bool)->A#B`) THEN
  REWRITE_TAC[CONJUNCT1 prod_tybij] THEN DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY EXISTS_TAC [`a:A`; `b:B`] THEN REFL_TAC);;

let FST = prove
 (`!(x:A) (y:B). FST(x,y) = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FST_DEF] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN GEN_TAC THEN BETA_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `y:B` THEN ASM_REWRITE_TAC[]);;

let SND = prove
 (`!(x:A) (y:B). SND(x,y) = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SND_DEF] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN GEN_TAC THEN BETA_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]);;

let PAIR = prove
 (`!x:A#B. FST x,SND x = x`,
  GEN_TAC THEN
  (X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:B` SUBST1_TAC)
     (SPEC `x:A#B` PAIR_SURJECTIVE)) THEN
  REWRITE_TAC[FST; SND]);;

let pair_INDUCT = prove
 (`!P:A#B->bool. (!x y. P (x,y)) ==> !p. P p`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM PAIR] THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);;

let pair_RECURSION = prove
 (`!PAIR'. ?fn:A#B->C. !a0 a1. fn (a0,a1) = PAIR' a0 a1`,
  GEN_TAC THEN EXISTS_TAC `\p. (PAIR':A->B->C) (FST p) (SND p)` THEN
  REWRITE_TAC[FST; SND]);;

(* ------------------------------------------------------------------------- *)
(* Syntax operations.                                                        *)
(* ------------------------------------------------------------------------- *)

let is_pair = is_binary ",";;

let dest_pair = dest_binary ",";;

let mk_pair =
  let ptm = mk_const(",",[]) in
  fun (l,r) -> mk_comb(mk_comb(inst [type_of l,aty; type_of r,bty] ptm,l),r);;

(* ------------------------------------------------------------------------- *)
(* Extend basic rewrites; extend new_definition to allow paired varstructs.  *)
(* ------------------------------------------------------------------------- *)

extend_basic_rewrites [FST; SND; PAIR];;

(* ------------------------------------------------------------------------- *)
(* Extend definitions to paired varstructs with benignity checking.          *)
(* ------------------------------------------------------------------------- *)

let the_definitions = ref
 [SND_DEF; FST_DEF; COMMA_DEF; mk_pair_def; GEQ_DEF; GABS_DEF;
  LET_END_DEF; LET_DEF; one_DEF; I_DEF; o_DEF; COND_DEF; _FALSITY_;
  EXISTS_UNIQUE_DEF; NOT_DEF; F_DEF; OR_DEF; EXISTS_DEF; FORALL_DEF; IMP_DEF;
  AND_DEF; T_DEF];;

let new_definition =
  let depair =
    let rec depair gv arg =
      try let l,r = dest_pair arg in
          (depair (list_mk_icomb "FST" [gv]) l) @
          (depair (list_mk_icomb "SND" [gv]) r)
      with Failure _ -> [gv,arg] in
    fun arg -> let gv = genvar(type_of arg) in
               gv,depair gv arg in
  fun tm ->
    let avs,def = strip_forall tm in
    try let th,th' = tryfind (fun th -> th,PART_MATCH I th def)
                             (!the_definitions) in
        ignore(PART_MATCH I th' (snd(strip_forall(concl th))));
        warn true "Benign redefinition"; GEN_ALL (GENL avs th')
    with Failure _ ->
        let l,r = dest_eq def in
        let fn,args = strip_comb l in
        let gargs,reps = (I F_F unions) (unzip(map depair args)) in
        let l' = list_mk_comb(fn,gargs) and r' = subst reps r in
        let th1 = new_definition (mk_eq(l',r')) in
        let slist = zip args gargs in
        let th2 = INST slist (SPEC_ALL th1) in
        let xreps = map (subst slist o fst) reps in
        let threps = map (SYM o PURE_REWRITE_CONV[FST; SND]) xreps in
        let th3 = TRANS th2 (SYM(SUBS_CONV threps r)) in
        let th4 = GEN_ALL (GENL avs th3) in
        the_definitions := th4::(!the_definitions); th4;;

(* ------------------------------------------------------------------------- *)
(* A few more useful definitions.                                            *)
(* ------------------------------------------------------------------------- *)

let CURRY_DEF = new_definition
 `CURRY(f:A#B->C) x y = f(x,y)`;;

let UNCURRY_DEF = new_definition
 `!f x y. UNCURRY(f:A->B->C)(x,y) = f x y`;;

let PASSOC_DEF = new_definition
 `!f x y z. PASSOC (f:(A#B)#C->D) (x,y,z) = f ((x,y),z)`;;

(* ------------------------------------------------------------------------- *)
(* Analog of ABS_CONV for generalized abstraction.                           *)
(* ------------------------------------------------------------------------- *)

let GABS_CONV conv tm =
  if is_abs tm then ABS_CONV conv tm else
  let gabs,bod = dest_comb tm in
  let f,qtm = dest_abs bod in
  let xs,bod = strip_forall qtm in
  AP_TERM gabs (ABS f (itlist MK_FORALL xs (RAND_CONV conv bod)));;

(* ------------------------------------------------------------------------- *)
(* General beta-conversion over linear pattern of nested constructors.       *)
(* ------------------------------------------------------------------------- *)

let GEN_BETA_CONV =
  let projection_cache = ref [] in
  let create_projections conname =
    try assoc conname (!projection_cache) with Failure _ ->
    let genty = get_const_type conname in
    let conty = fst(dest_type(repeat (snd o dest_fun_ty) genty)) in
    let _,_,rth = assoc conty (!inductive_type_store) in
    let sth = SPEC_ALL rth in
    let evs,bod = strip_exists(concl sth) in
    let cjs = conjuncts bod in
    let ourcj = find ((=)conname o fst o dest_const o fst o strip_comb o
                      rand o lhand o snd o strip_forall) cjs in
    let n = index ourcj cjs in
    let avs,eqn = strip_forall ourcj in
    let con',args = strip_comb(rand eqn) in
    let aargs,zargs = chop_list (length avs) args in
    let gargs = map (genvar o type_of) zargs in
    let gcon = genvar(itlist (mk_fun_ty o type_of) avs (type_of(rand eqn))) in
    let bth =
      INST [list_mk_abs(aargs @ gargs,list_mk_comb(gcon,avs)),con'] sth in
    let cth = el n (CONJUNCTS(ASSUME(snd(strip_exists(concl bth))))) in
    let dth = CONV_RULE (funpow (length avs) BINDER_CONV
      (RAND_CONV(BETAS_CONV))) cth in
    let eth = SIMPLE_EXISTS (rator(lhand(snd(strip_forall(concl dth))))) dth in
    let fth = PROVE_HYP bth (itlist SIMPLE_CHOOSE evs eth) in
    let zty = type_of (rand(snd(strip_forall(concl dth)))) in
    let mk_projector a =
      let ity = type_of a in
      let th = BETA_RULE(PINST [ity,zty] [list_mk_abs(avs,a),gcon] fth) in
      SYM(SPEC_ALL(SELECT_RULE th)) in
    let ths = map mk_projector avs in
    (projection_cache := (conname,ths)::(!projection_cache); ths) in
  let GEQ_CONV = REWR_CONV(GSYM GEQ_DEF)
  and DEGEQ_RULE = CONV_RULE(REWR_CONV GEQ_DEF) in
  let GABS_RULE =
    let pth = prove
     (`(?) P ==> P (GABS P)`,
      SIMP_TAC[GABS_DEF; SELECT_AX; ETA_AX]) in
    MATCH_MP pth in
  let rec create_iterated_projections tm =
    if frees tm = [] then []
    else if is_var tm then [REFL tm] else
    let con,args = strip_comb tm in
    let prjths = create_projections (fst(dest_const con)) in
    let atm = rand(rand(concl(hd prjths))) in
    let instn = term_match [] atm tm in
    let arths = map (INSTANTIATE instn) prjths in
    let ths = map (fun arth ->
      let sths = create_iterated_projections (lhand(concl arth)) in
      map (CONV_RULE(RAND_CONV(SUBS_CONV[arth]))) sths) arths in
    unions' equals_thm ths in
  let GEN_BETA_CONV tm =
    try BETA_CONV tm with Failure _ ->
    let l,r = dest_comb tm in
    let vstr,bod = dest_gabs l in
    let instn = term_match [] vstr r in
    let prjs = create_iterated_projections vstr in
    let th1 = SUBS_CONV prjs bod in
    let bod' = rand(concl th1) in
    let gv = genvar(type_of vstr) in
    let pat = mk_abs(gv,subst[gv,vstr] bod') in
    let th2 = TRANS (BETA_CONV (mk_comb(pat,vstr))) (SYM th1) in
    let avs = fst(strip_forall(body(rand l))) in
    let th3 = GENL (fst(strip_forall(body(rand l)))) th2 in
    let efn = genvar(type_of pat) in
    let th4 = EXISTS(mk_exists(efn,subst[efn,pat] (concl th3)),pat) th3 in
    let th5 = CONV_RULE(funpow (length avs + 1) BINDER_CONV GEQ_CONV) th4 in
    let th6 = CONV_RULE BETA_CONV (GABS_RULE th5) in
    INSTANTIATE instn (DEGEQ_RULE (SPEC_ALL th6)) in
  GEN_BETA_CONV;;

(* ------------------------------------------------------------------------- *)
(* Add this to the basic "rewrites" and pairs to the inductive type store.   *)
(* ------------------------------------------------------------------------- *)

extend_basic_convs("GEN_BETA_CONV",(`GABS (\a. b) c`,GEN_BETA_CONV));;

inductive_type_store :=
 ("prod",(1,pair_INDUCT,pair_RECURSION))::(!inductive_type_store);;

(* ------------------------------------------------------------------------- *)
(* Convenient rules to eliminate binders over pairs.                         *)
(* ------------------------------------------------------------------------- *)

let FORALL_PAIR_THM = prove
 (`!P:A#B->bool. (!p. P p) <=> (!p1 p2. P(p1,p2))`,
  MESON_TAC[PAIR]);;

let EXISTS_PAIR_THM = prove
 (`!P:A#B->bool. (?p. P p) <=> ?p1 p2. P(p1,p2)`,
  MESON_TAC[PAIR]);;

let LAMBDA_PAIR_THM = prove
 (`!t:A#B->C. (\p. t p) = (\(x,y). t(x,y))`,
  REWRITE_TAC[FORALL_PAIR_THM; FUN_EQ_THM]);;

let LAMBDA_PAIR = prove
 (`!f:A->B->C. (\(x,y). f x y) = (\p. f (FST p) (SND p))`,
  REWRITE_TAC[LAMBDA_PAIR_THM]);;

let LAMBDA_TRIPLE_THM = prove
 (`!f:A#B#C->D. (\t. f t) = (\(x,y,z). f(x,y,z))`,
  REWRITE_TAC[FORALL_PAIR_THM; FUN_EQ_THM]);;

let LAMBDA_TRIPLE = prove
 (`!f:A->B->C->D.
   (\(x,y,z). f x y z) = (\t. f (FST t) (FST(SND t)) (SND(SND t)))`,
  REWRITE_TAC[LAMBDA_TRIPLE_THM]);;

let PAIRED_ETA_THM = prove
 (`(!f:A#B->C. (\(x,y). f (x,y)) = f) /\
   (!f:A#B#C->D. (\(x,y,z). f (x,y,z)) = f) /\
   (!f:A#B#C#D->E. (\(w,x,y,z). f (w,x,y,z)) = f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]);;

let FORALL_UNCURRY = prove
 (`!P. (!f:A->B->C. P f) <=> (!f. P (\a b. f(a,b)))`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  X_GEN_TAC `f:A->B->C` THEN
  FIRST_ASSUM(MP_TAC o SPEC `\(a,b). (f:A->B->C) a b`) THEN SIMP_TAC[ETA_AX]);;

let EXISTS_UNCURRY = prove
 (`!P. (?f:A->B->C. P f) <=> (?f. P (\a b. f(a,b)))`,
  ONCE_REWRITE_TAC[MESON[] `(?x. P x) <=> ~(!x. ~P x)`] THEN
  REWRITE_TAC[FORALL_UNCURRY]);;

let EXISTS_CURRY = prove
 (`!P:(A#B->C)->bool. (?f. P f) <=> (?f. P (\(a,b). f a b))`,
  REWRITE_TAC[EXISTS_UNCURRY; PAIRED_ETA_THM]);;

let FORALL_CURRY = prove
 (`!P:(A#B->C)->bool. (!f. P f) <=> (!f. P (\(a,b). f a b))`,
  REWRITE_TAC[FORALL_UNCURRY; PAIRED_ETA_THM]);;

let FORALL_UNPAIR_THM = prove
 (`!P:A->B->bool. (!x y. P x y) <=> !z. P (FST z) (SND z)`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN MESON_TAC[]);;

let EXISTS_UNPAIR_THM = prove
 (`!P:A->B->bool. (?x y. P x y) <=> ?z. P (FST z) (SND z)`,
  REWRITE_TAC[EXISTS_PAIR_THM; FST; SND] THEN MESON_TAC[]);;

let FORALL_PAIR_FUN_THM = prove
 (`!P. (!f:A->B#C. P f) <=> (!g h. P(\a. g a,h a))`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN
  GEN_REWRITE_TAC BINDER_CONV [GSYM PAIR] THEN PURE_ASM_REWRITE_TAC[]);;

let EXISTS_PAIR_FUN_THM = prove
 (`!P. (?f:A->B#C. P f) <=> (?g h. P(\a. g a,h a))`,
  REWRITE_TAC[MESON[] `(?x. P x) <=> ~(!x. ~P x)`] THEN
  REWRITE_TAC[FORALL_PAIR_FUN_THM]);;

let FORALL_UNPAIR_FUN_THM = prove
 (`!P:(A->B)->(A->C)->bool. (!f g. P f g) <=> (!h. P (FST o h) (SND o h))`,
  REWRITE_TAC[FORALL_PAIR_FUN_THM; o_DEF; ETA_AX]);;

let EXISTS_UNPAIR_FUN_THM = prove
 (`!P:(A->B)->(A->C)->bool. (?f g. P f g) <=> (?h. P (FST o h) (SND o h))`,
  REWRITE_TAC[EXISTS_PAIR_FUN_THM; o_DEF; ETA_AX]);;

let EXISTS_SWAP_FUN_THM = prove
 (`!P:(A->B->C)->bool. (?f. P f) <=> (?f. P (\a b. f b a))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_TAC `f:A->B->C`) THEN
    EXISTS_TAC `\b a. (f:A->B->C) a b`;
    DISCH_THEN(X_CHOOSE_TAC `f:B->A->C`) THEN
    EXISTS_TAC `\b a. (f:B->A->C) a b`] THEN
  ASM_REWRITE_TAC[ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Related theorems for explicitly paired quantifiers.                       *)
(* ------------------------------------------------------------------------- *)

let FORALL_PAIRED_THM = prove
 (`!P:A->B->bool. (!(x,y). P x y) <=> (!x y. P x y)`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [FORALL_DEF] THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]);;

let EXISTS_PAIRED_THM = prove
 (`!P:A->B->bool. (?(x,y). P x y) <=> (?x y. P x y)`,
  GEN_TAC THEN MATCH_MP_TAC(TAUT `(~p <=> ~q) ==> (p <=> q)`) THEN
  REWRITE_TAC[REWRITE_RULE[ETA_AX] NOT_EXISTS_THM; FORALL_PAIR_THM]);;

(* ------------------------------------------------------------------------- *)
(* Likewise for tripled quantifiers (could continue with the same proof).    *)
(* ------------------------------------------------------------------------- *)

let FORALL_TRIPLED_THM = prove
 (`!P:A->B->C->bool. (!(x,y,z). P x y z) <=> (!x y z. P x y z)`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [FORALL_DEF] THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]);;

let EXISTS_TRIPLED_THM = prove
 (`!P:A->B->C->bool. (?(x,y,z). P x y z) <=> (?x y z. P x y z)`,
  GEN_TAC THEN MATCH_MP_TAC(TAUT `(~p <=> ~q) ==> (p <=> q)`) THEN
  REWRITE_TAC[REWRITE_RULE[ETA_AX] NOT_EXISTS_THM; FORALL_PAIR_THM]);;

(* ------------------------------------------------------------------------- *)
(* Similar theorems for the choice operator.                                 *)
(* ------------------------------------------------------------------------- *)

let CHOICE_UNPAIR_THM = prove
 (`!P. (@(x:A,y:B). P x y) = (@p. P (FST p) (SND p))`,
  REWRITE_TAC[LAMBDA_PAIR]);;

let CHOICE_PAIRED_THM = prove
 (`!P Q. (?x:A y:B. P x y) /\ (!x y. P x y ==> Q(x,y)) ==> Q (@(x,y). P x y)`,
  INTRO_TAC "!P Q; (@x0 y0. P0) PQ" THEN
  SUBGOAL_THEN `(\ (x:A,y:B). P x y:bool) = (\p. P (FST p) (SND p))`
    SUBST1_TAC THENL
  [REWRITE_TAC[LAMBDA_PAIR_THM]; SELECT_ELIM_TAC] THEN
  INTRO_TAC "![c]; c" THEN ONCE_REWRITE_TAC[GSYM PAIR] THEN
  REMOVE_THEN "PQ" MATCH_MP_TAC THEN REMOVE_THEN "c" MATCH_MP_TAC THEN
  REWRITE_TAC[EXISTS_PAIR_THM] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Expansion of a let-term.                                                  *)
(* ------------------------------------------------------------------------- *)

let let_CONV =
  let let1_CONV = REWR_CONV LET_DEF THENC GEN_BETA_CONV
  and lete_CONV = REWR_CONV LET_END_DEF in
  let rec EXPAND_BETAS_CONV tm =
    let tm' = rator tm in
    try let1_CONV tm with Failure _ ->
    let th1 = AP_THM (EXPAND_BETAS_CONV tm') (rand tm) in
    let th2 = GEN_BETA_CONV (rand(concl th1)) in
    TRANS th1 th2 in
  fun tm ->
    let ltm,pargs = strip_comb tm in
    if fst(dest_const ltm) <> "LET" || pargs = [] then failwith "let_CONV" else
    let abstm = hd pargs in
    let vs,bod = strip_gabs abstm in
    let es = tl pargs in
    let n = length es in
    if length vs <> n then failwith "let_CONV" else
    (EXPAND_BETAS_CONV THENC lete_CONV) tm;;

let (LET_TAC:tactic) =
  let is_trivlet tm =
    try let assigs,bod = dest_let tm in
        forall (uncurry (=)) assigs
    with Failure _ -> false
  and PROVE_DEPAIRING_EXISTS =
    let pth = prove
     (`((x,y) = a) <=> (x = FST a) /\ (y = SND a)`,
      MESON_TAC[PAIR; PAIR_EQ]) in
    let rewr1_CONV = GEN_REWRITE_CONV TOP_DEPTH_CONV [pth]
    and rewr2_RULE = GEN_REWRITE_RULE (LAND_CONV o DEPTH_CONV)
                      [TAUT `(x = x) <=> T`; TAUT `a /\ T <=> a`] in
    fun tm ->
      let th1 = rewr1_CONV tm in
      let tm1 = rand(concl th1) in
      let cjs = conjuncts tm1 in
      let vars = map lhand cjs in
      let th2 = EQ_MP (SYM th1) (ASSUME tm1) in
      let th3 = DISCH_ALL (itlist SIMPLE_EXISTS vars th2) in
      let th4 = INST (map (fun t -> rand t,lhand t) cjs) th3 in
      MP (rewr2_RULE th4) TRUTH in
  fun (asl,w as gl) ->
    let path = try find_path is_trivlet w
               with Failure _ -> find_path is_let w in
    let tm = follow_path path w in
    let assigs,bod = dest_let tm in
    let abbrevs =
      mapfilter (fun (x,y) -> if x = y then fail() else mk_eq(x,y)) assigs in
    let lvars = itlist (union o frees o lhs) abbrevs []
    and avoids = itlist (union o thm_frees o snd) asl (frees w) in
    let rename = vsubst (zip (variants avoids lvars) lvars) in
    let abbrevs' = map (fun eq -> let l,r = dest_eq eq in mk_eq(rename l,r))
                       abbrevs in
    let deprths = map PROVE_DEPAIRING_EXISTS abbrevs' in
    (MAP_EVERY (REPEAT_TCL CHOOSE_THEN
       (fun th -> let th' = SYM th in
                  SUBST_ALL_TAC th' THEN ASSUME_TAC th')) deprths THEN
     W(fun (asl',w') ->
        let tm' = follow_path path w' in
        CONV_TAC(PATH_CONV path (K(let_CONV tm'))))) gl;;

(* ------------------------------------------------------------------------- *)
(* Apply conversion "conv" to RHS of toplevel let-term                       *)
(* ------------------------------------------------------------------------- *)

let SUBLET_CONV conv =
  let rec largconv tm =
    match tm with
      Comb(Const("LET",_),_) -> REFL tm
    | Comb(l,r) -> (COMB2_CONV largconv conv) tm
    | _ -> failwith "SUBLET_CONV" in
  fun tm -> if is_let tm then largconv tm
            else failwith "SUBLET_CONV";;
