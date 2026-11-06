(* ========================================================================= *)
(* Inductive (or free recursive) types.                                      *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "grobner.ml";;

(* ------------------------------------------------------------------------- *)
(* Abstract left inverses for binary injections (we could construct them...) *)
(* ------------------------------------------------------------------------- *)

let INJ_INVERSE2 = prove
 (`!P:A->B->C.
    (!x1 y1 x2 y2. (P x1 y1 = P x2 y2) <=> (x1 = x2) /\ (y1 = y2))
    ==> ?X Y. !x y. (X(P x y) = x) /\ (Y(P x y) = y)`,
  GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `\z:C. @x:A. ?y:B. P x y = z` THEN
  EXISTS_TAC `\z:C. @y:B. ?x:A. P x y = z` THEN
  REPEAT GEN_TAC THEN ASM_REWRITE_TAC[BETA_THM] THEN
  CONJ_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN GEN_TAC THEN BETA_TAC THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  W(EXISTS_TAC o rand o snd o dest_exists o snd) THEN REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Define an injective pairing function on ":num".                           *)
(* ------------------------------------------------------------------------- *)

let NUMPAIR = new_definition
  `NUMPAIR x y = (2 EXP x) * (2 * y + 1)`;;

let NUMPAIR_INJ_LEMMA = prove
 (`!x1 y1 x2 y2. (NUMPAIR x1 y1 = NUMPAIR x2 y2) ==> (x1 = x2)`,
  REWRITE_TAC[NUMPAIR] THEN REPEAT(INDUCT_TAC THEN GEN_TAC) THEN
  ASM_REWRITE_TAC[EXP; GSYM MULT_ASSOC; ARITH; EQ_MULT_LCANCEL;
    NOT_SUC; GSYM NOT_SUC; SUC_INJ] THEN
  DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
  REWRITE_TAC[EVEN_MULT; EVEN_ADD; ARITH]);;

let NUMPAIR_INJ = prove
 (`!x1 y1 x2 y2. (NUMPAIR x1 y1 = NUMPAIR x2 y2) <=> (x1 = x2) /\ (y1 = y2)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP NUMPAIR_INJ_LEMMA) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[NUMPAIR] THEN
  REWRITE_TAC[EQ_MULT_LCANCEL; EQ_ADD_RCANCEL; EXP_EQ_0; ARITH]);;

let NUMPAIR_DEST = new_specification
  ["NUMFST"; "NUMSND"]
  (MATCH_MP INJ_INVERSE2 NUMPAIR_INJ);;

(* ------------------------------------------------------------------------- *)
(* Also, an injective map bool->num->num (even easier!)                      *)
(* ------------------------------------------------------------------------- *)

let NUMSUM = new_definition
  `NUMSUM b x = if b then SUC(2 * x) else 2 * x`;;

let NUMSUM_INJ = prove
 (`!b1 x1 b2 x2. (NUMSUM b1 x1 = NUMSUM b2 x2) <=> (b1 = b2) /\ (x1 = x2)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(MP_TAC o REWRITE_RULE[NUMSUM]) THEN
  DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC(AP_TERM `EVEN` th)) THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[EVEN; EVEN_DOUBLE] THEN
  REWRITE_TAC[SUC_INJ; EQ_MULT_LCANCEL; ARITH]);;

let NUMSUM_DEST = new_specification
  ["NUMLEFT"; "NUMRIGHT"]
  (MATCH_MP INJ_INVERSE2 NUMSUM_INJ);;

(* ------------------------------------------------------------------------- *)
(* Injection num->Z, where Z == num->A->bool.                                *)
(* ------------------------------------------------------------------------- *)

let INJN = new_definition
 `INJN (m:num) = \(n:num) (a:A). n = m`;;

let INJN_INJ = prove
 (`!n1 n2. (INJN n1 :num->A->bool = INJN n2) <=> (n1 = n2)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(MP_TAC o C AP_THM `n1:num` o REWRITE_RULE[INJN]) THEN
  DISCH_THEN(MP_TAC o C AP_THM `a:A`) THEN REWRITE_TAC[BETA_THM]);;

(* ------------------------------------------------------------------------- *)
(* Injection A->Z, where Z == num->A->bool.                                  *)
(* ------------------------------------------------------------------------- *)

let INJA = new_definition
 `INJA (a:A) = \(n:num) b. b = a`;;

let INJA_INJ = prove
 (`!a1 a2. (INJA a1 = INJA a2) <=> (a1:A = a2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INJA; FUN_EQ_THM] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `a1:A`) THEN REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Injection (num->Z)->Z, where Z == num->A->bool.                           *)
(* ------------------------------------------------------------------------- *)

let INJF = new_definition
  `INJF (f:num->(num->A->bool)) = \n. f (NUMFST n) (NUMSND n)`;;

let INJF_INJ = prove
 (`!f1 f2. (INJF f1 :num->A->bool = INJF f2) <=> (f1 = f2)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `m:num`; `a:A`] THEN
  POP_ASSUM(MP_TAC o REWRITE_RULE[INJF]) THEN
  DISCH_THEN(MP_TAC o C AP_THM `a:A` o C AP_THM `NUMPAIR n m`) THEN
  REWRITE_TAC[NUMPAIR_DEST]);;

(* ------------------------------------------------------------------------- *)
(* Injection Z->Z->Z, where Z == num->A->bool.                               *)
(* ------------------------------------------------------------------------- *)

let INJP = new_definition
  `INJP f1 f2:num->A->bool =
        \n a. if NUMLEFT n then f1 (NUMRIGHT n) a else f2 (NUMRIGHT n) a`;;

let INJP_INJ = prove
 (`!(f1:num->A->bool) f1' f2 f2'.
        (INJP f1 f2 = INJP f1' f2') <=> (f1 = f1') /\ (f2 = f2')`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[FUN_EQ_THM] THEN REWRITE_TAC[AND_FORALL_THM] THEN
  X_GEN_TAC `n:num` THEN POP_ASSUM(MP_TAC o REWRITE_RULE[INJP]) THEN
  DISCH_THEN(MP_TAC o GEN `b:bool` o C AP_THM `NUMSUM b n`) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `T` th) THEN MP_TAC(SPEC `F` th)) THEN
  ASM_SIMP_TAC[NUMSUM_DEST; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Now, set up "constructor" and "bottom" element.                           *)
(* ------------------------------------------------------------------------- *)

let ZCONSTR = new_definition
  `ZCONSTR c i r :num->A->bool
     = INJP (INJN (SUC c)) (INJP (INJA i) (INJF r))`;;

let ZBOT = new_definition
  `ZBOT = INJP (INJN 0) (@z:num->A->bool. T)`;;

let ZCONSTR_ZBOT = prove
 (`!c i r. ~(ZCONSTR c i r :num->A->bool = ZBOT)`,
  REWRITE_TAC[ZCONSTR; ZBOT; INJP_INJ; INJN_INJ; NOT_SUC]);;

(* ------------------------------------------------------------------------- *)
(* Carve out an inductively defined set.                                     *)
(* ------------------------------------------------------------------------- *)

let ZRECSPACE_RULES,ZRECSPACE_INDUCT,ZRECSPACE_CASES =
  new_inductive_definition
   `ZRECSPACE (ZBOT:num->A->bool) /\
    (!c i r. (!n. ZRECSPACE (r n)) ==> ZRECSPACE (ZCONSTR c i r))`;;

let recspace_tydef =
  new_basic_type_definition "recspace" ("_mk_rec","_dest_rec")
  (CONJUNCT1 ZRECSPACE_RULES);;

(* ------------------------------------------------------------------------- *)
(* Define lifted constructors.                                               *)
(* ------------------------------------------------------------------------- *)

let BOTTOM = new_definition
  `BOTTOM = _mk_rec (ZBOT:num->A->bool)`;;

let CONSTR = new_definition
  `CONSTR c i r :(A)recspace
     = _mk_rec (ZCONSTR c i (\n. _dest_rec(r n)))`;;

(* ------------------------------------------------------------------------- *)
(* Some lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

let MK_REC_INJ = prove
 (`!x y. (_mk_rec x :(A)recspace = _mk_rec y)
         ==> (ZRECSPACE x /\ ZRECSPACE y ==> (x = y))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[snd recspace_tydef] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
  ASM_REWRITE_TAC[]);;

let DEST_REC_INJ = prove
 (`!x y. (_dest_rec x = _dest_rec y) <=> (x:(A)recspace = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(MP_TAC o AP_TERM
    `_mk_rec:(num->A->bool)->(A)recspace`) THEN
  REWRITE_TAC[fst recspace_tydef]);;

(* ------------------------------------------------------------------------- *)
(* Show that the set is freely inductively generated.                        *)
(* ------------------------------------------------------------------------- *)

let CONSTR_BOT = prove
 (`!c i r. ~(CONSTR c i r :(A)recspace = BOTTOM)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONSTR; BOTTOM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MK_REC_INJ) THEN
  REWRITE_TAC[ZCONSTR_ZBOT; ZRECSPACE_RULES] THEN
  MATCH_MP_TAC(CONJUNCT2 ZRECSPACE_RULES) THEN
  REWRITE_TAC[fst recspace_tydef; snd recspace_tydef]);;

let CONSTR_INJ = prove
 (`!c1 i1 r1 c2 i2 r2. (CONSTR c1 i1 r1 :(A)recspace = CONSTR c2 i2 r2) <=>
                       (c1 = c2) /\ (i1 = i2) /\ (r1 = r2)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(MP_TAC o REWRITE_RULE[CONSTR]) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MK_REC_INJ) THEN
  W(C SUBGOAL_THEN ASSUME_TAC o funpow 2 lhand o snd) THENL
   [CONJ_TAC THEN MATCH_MP_TAC(CONJUNCT2 ZRECSPACE_RULES) THEN
    REWRITE_TAC[fst recspace_tydef; snd recspace_tydef];
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[ZCONSTR] THEN
    REWRITE_TAC[INJP_INJ; INJN_INJ; INJF_INJ; INJA_INJ] THEN
    ONCE_REWRITE_TAC[FUN_EQ_THM] THEN BETA_TAC THEN
    REWRITE_TAC[SUC_INJ; DEST_REC_INJ]]);;

let CONSTR_IND = prove
 (`!P. P(BOTTOM) /\
       (!c i r. (!n. P(r n)) ==> P(CONSTR c i r))
       ==> !x:(A)recspace. P(x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `\z:num->A->bool. ZRECSPACE(z) /\ P(_mk_rec z)`
         ZRECSPACE_INDUCT) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[ZRECSPACE_RULES; GSYM BOTTOM] THEN
  W(C SUBGOAL_THEN ASSUME_TAC o funpow 2 lhand o snd) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[FORALL_AND_THM] THEN
    REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC(CONJUNCT2 ZRECSPACE_RULES) THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(ANTE_RES_THEN MP_TAC) THEN
      REWRITE_TAC[CONSTR] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[snd recspace_tydef]) THEN
      ASM_SIMP_TAC[ETA_AX]];
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `_dest_rec (x:(A)recspace)`) THEN
    REWRITE_TAC[fst recspace_tydef] THEN
    REWRITE_TAC[ITAUT `(a ==> a /\ b) <=> (a ==> b)`] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[fst recspace_tydef; snd recspace_tydef]]);;

(* ------------------------------------------------------------------------- *)
(* Now prove the recursion theorem (this subcase is all we need).            *)
(* ------------------------------------------------------------------------- *)

let CONSTR_REC = prove
 (`!Fn:num->A->(num->(A)recspace)->(num->B)->B.
     ?f. (!c i r. f (CONSTR c i r) = Fn c i r (\n. f (r n)))`,
  REPEAT STRIP_TAC THEN (MP_TAC o prove_inductive_relations_exist)
    `(Z:(A)recspace->B->bool) BOTTOM b /\
     (!c i r y. (!n. Z (r n) (y n)) ==> Z (CONSTR c i r) (Fn c i r y))` THEN
  DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o GSYM)) THEN
  SUBGOAL_THEN `!x. ?!y. (Z:(A)recspace->B->bool) x y` MP_TAC THENL
   [W(MP_TAC o PART_MATCH rand CONSTR_IND o snd) THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
     [FIRST_ASSUM(fun t -> GEN_REWRITE_TAC BINDER_CONV [GSYM t]) THEN
      REWRITE_TAC[GSYM CONSTR_BOT; EXISTS_UNIQUE_REFL];
      DISCH_THEN(MP_TAC o REWRITE_RULE[EXISTS_UNIQUE_THM; FORALL_AND_THM]) THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN(MP_TAC o REWRITE_RULE[SKOLEM_THM]) THEN
      DISCH_THEN(X_CHOOSE_THEN `y:num->B` ASSUME_TAC) THEN
      REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
      FIRST_ASSUM(fun th -> CHANGED_TAC(ONCE_REWRITE_TAC[GSYM th])) THEN
      CONJ_TAC THENL
       [EXISTS_TAC `(Fn:num->A->(num->(A)recspace)->(num->B)->B) c i r y` THEN
        REWRITE_TAC[CONSTR_BOT; CONSTR_INJ; GSYM CONJ_ASSOC] THEN
        REWRITE_TAC[UNWIND_THM1; RIGHT_EXISTS_AND_THM] THEN
        EXISTS_TAC `y:num->B` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[CONSTR_BOT; CONSTR_INJ; GSYM CONJ_ASSOC] THEN
        REWRITE_TAC[UNWIND_THM1; RIGHT_EXISTS_AND_THM] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT AP_TERM_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
        X_GEN_TAC `w:num` THEN FIRST_ASSUM MATCH_MP_TAC THEN
        EXISTS_TAC `w:num` THEN ASM_REWRITE_TAC[]]];
    REWRITE_TAC[UNIQUE_SKOLEM_ALT] THEN
    DISCH_THEN(X_CHOOSE_THEN `fn:(A)recspace->B` (ASSUME_TAC o GSYM)) THEN
    EXISTS_TAC `fn:(A)recspace->B` THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN
    REWRITE_TAC[BETA_THM]]);;

(* ------------------------------------------------------------------------- *)
(* The following is useful for coding up functions casewise.                 *)
(* ------------------------------------------------------------------------- *)

let FCONS = new_recursive_definition num_RECURSION
 `(!a f. FCONS (a:A) f 0 = a) /\
  (!a f n. FCONS (a:A) f (SUC n) = f n)`;;

let FCONS_UNDO = prove
 (`!f:num->A. f = FCONS (f 0) (f o SUC)`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  INDUCT_TAC THEN REWRITE_TAC[FCONS; o_THM]);;

let FNIL = new_definition
  `FNIL (n:num) = @x:A. T`;;

(* ------------------------------------------------------------------------- *)
(* The initial mutual type definition function, with a type-restricted       *)
(* recursion theorem.                                                        *)
(* ------------------------------------------------------------------------- *)

let define_type_raw =

  (* ----------------------------------------------------------------------- *)
  (* Handy utility to produce "SUC o SUC o SUC ..." form of numeral.         *)
  (* ----------------------------------------------------------------------- *)

  let sucivate =
    let zero = `0` and suc = `SUC` in
    fun n -> funpow n (curry mk_comb suc) zero in

  (* ----------------------------------------------------------------------- *)
  (* Eliminate local "definitions" in hyps.                                  *)
  (* ----------------------------------------------------------------------- *)


  let SCRUB_EQUATION eq (th,insts) = (*HA*)
    let eq' = itlist subst (map (fun t -> [t]) insts) eq in
    let l,r = dest_eq eq' in
    (MP (INST [r,l] (DISCH eq' th)) (REFL r),(r,l)::insts) in

  (* ----------------------------------------------------------------------- *)
  (* Proves existence of model (inductively); use pseudo-constructors.       *)
  (*                                                                         *)
  (* Returns suitable definitions of constructors in terms of CONSTR, and    *)
  (* the rule and induction theorems from the inductive relation package.    *)
  (* ----------------------------------------------------------------------- *)

  let justify_inductive_type_model =
    let t_tm = `T` and n_tm = `n:num` and beps_tm = `@x:bool. T` in
    let rec munion s1 s2 =
      if s1 = [] then s2 else
      let h1 = hd s1
      and s1' = tl s1 in
      try let _,s2' = remove (fun h2 -> h2 = h1) s2 in h1::(munion s1' s2')
      with Failure _ -> h1::(munion s1' s2) in
    fun def ->
      let newtys,rights = unzip def in
      let tyargls = itlist ((@) o map snd) rights [] in
      let alltys = itlist (munion o C subtract newtys) tyargls [] in
      let epstms = map (fun ty -> mk_select(mk_var("v",ty),t_tm)) alltys in
      let pty =
        try end_itlist (fun ty1 ty2 -> mk_type("prod",[ty1;ty2])) alltys
        with Failure _ -> bool_ty in
      let recty = mk_type("recspace",[pty]) in
      let constr = mk_const("CONSTR",[pty,aty]) in
      let fcons = mk_const("FCONS",[recty,aty]) in
      let bot = mk_const("BOTTOM",[pty,aty]) in
      let bottail = mk_abs(n_tm,bot) in
      let mk_constructor n (cname,cargs) =
        let ttys = map (fun ty -> if mem ty newtys then recty else ty) cargs in
        let args = make_args "a" [] ttys in
        let rargs,iargs = partition (fun t -> type_of t = recty) args in
        let rec mk_injector epstms alltys iargs =
          if alltys = [] then [] else
          let ty = hd alltys in
          try let a,iargs' = remove (fun t -> type_of t = ty) iargs in
              a::(mk_injector (tl epstms) (tl alltys) iargs')
          with Failure _ ->
              (hd epstms)::(mk_injector (tl epstms) (tl alltys) iargs) in
        let iarg =
          try end_itlist (curry mk_pair) (mk_injector epstms alltys iargs)
          with Failure _ -> beps_tm in
        let rarg = itlist (mk_binop fcons) rargs bottail in
      let conty = itlist mk_fun_ty (map type_of args) recty in
      let condef = list_mk_comb(constr,[sucivate n; iarg; rarg]) in
      mk_eq(mk_var(cname,conty),list_mk_abs(args,condef)) in
    let rec mk_constructors n rights =
      if rights = [] then [] else
      (mk_constructor n (hd rights))::(mk_constructors (n + 1) (tl rights)) in
    let condefs = mk_constructors 0 (itlist (@) rights []) in
    let conths = map ASSUME condefs in
    let predty = mk_fun_ty recty bool_ty in
    let edefs = itlist (fun (x,l) acc -> map (fun t -> x,t) l @ acc) def [] in
    let idefs = map2 (fun (r,(_,atys)) def -> (r,atys),def) edefs condefs in
    let mk_rule ((r,a),condef) =
      let left,right = dest_eq condef in
      let args,bod = strip_abs right in
      let lapp = list_mk_comb(left,args) in
      let conds = itlist2
        (fun arg argty sofar ->
          if mem argty newtys then
            mk_comb(mk_var(dest_vartype argty,predty),arg)::sofar
          else sofar) args a [] in
      let conc = mk_comb(mk_var(dest_vartype r,predty),lapp) in
      let rule = if conds = [] then conc
                 else mk_imp(list_mk_conj conds,conc) in
      list_mk_forall(args,rule) in
    let rules = list_mk_conj (map mk_rule idefs) in
    let th0 = derive_nonschematic_inductive_relations rules in
    let th1 = prove_monotonicity_hyps th0 in
    let th2a,th2bc = CONJ_PAIR th1 in
    let th2b = CONJUNCT1 th2bc in
    conths,th2a,th2b in

  (* ----------------------------------------------------------------------- *)
  (* Shows that the predicates defined by the rules are all nonempty.        *)
  (* (This could be done much more efficiently/cleverly, but it's OK.)       *)
  (* ----------------------------------------------------------------------- *)

  let prove_model_inhabitation rth =
    let srules = map SPEC_ALL (CONJUNCTS rth) in
    let imps,bases = partition (is_imp o concl) srules in
    let concs = map concl bases @ map (rand o concl) imps in
    let preds = setify (map (repeat rator) concs) in
    let rec exhaust_inhabitations ths sofar =
      let dunnit = setify(map (fst o strip_comb o concl) sofar) in
      let useful = filter
        (fun th -> not (mem (fst(strip_comb(rand(concl th)))) dunnit)) ths in
      if useful = [] then sofar else
      let follow_horn thm =
        let preds = map (fst o strip_comb) (conjuncts(lhand(concl thm))) in
        let asms = map
          (fun p -> find (fun th -> fst(strip_comb(concl th)) = p) sofar)
          preds in
        MATCH_MP thm (end_itlist CONJ asms) in
      let newth = tryfind follow_horn useful in
      exhaust_inhabitations ths (newth::sofar) in
    let ithms = exhaust_inhabitations imps bases in
    let exths = map
      (fun p -> find (fun th -> fst(strip_comb(concl th)) = p) ithms) preds in
    exths in

  (* ----------------------------------------------------------------------- *)
  (* Makes a type definition for one of the defined subsets.                 *)
  (* ----------------------------------------------------------------------- *)

  let define_inductive_type cdefs exth =
    let extm = concl exth in
    let epred = fst(strip_comb extm) in
    let ename = fst(dest_var epred) in
    let th1 = ASSUME (find (fun eq -> lhand eq = epred) (hyp exth)) in
    let th2 = TRANS th1 (SUBS_CONV cdefs (rand(concl th1))) in
    let th3 = EQ_MP (AP_THM th2 (rand extm)) exth in
    let th4,_ = itlist SCRUB_EQUATION (hyp th3) (th3,[]) in
    let mkname = "_mk_"^ename and destname = "_dest_"^ename in
    let bij1,bij2 = new_basic_type_definition ename (mkname,destname) th4 in
    let bij2a = AP_THM th2 (rand(rand(concl bij2))) in
    let bij2b = TRANS bij2a bij2 in
    bij1,bij2b in

  (* ----------------------------------------------------------------------- *)
  (* Defines a type constructor corresponding to current pseudo-constructor. *)
  (* ----------------------------------------------------------------------- *)

  let define_inductive_type_constructor defs consindex th =
    let avs,bod = strip_forall(concl th) in
    let asms,conc =
      if is_imp bod then conjuncts(lhand bod),rand bod else [],bod in
    let asmlist = map dest_comb asms in
    let cpred,cterm = dest_comb conc in
    let oldcon,oldargs = strip_comb cterm in
    let modify_arg v =
      try let dest = snd(assoc (rev_assoc v asmlist) consindex) in
          let ty' = hd(snd(dest_type(type_of dest))) in
          let v' = mk_var(fst(dest_var v),ty') in
          mk_comb(dest,v'),v'
      with Failure _ -> v,v in
    let newrights,newargs = unzip(map modify_arg oldargs) in
    let retmk = fst(assoc cpred consindex) in
    let defbod = mk_comb(retmk,list_mk_comb(oldcon,newrights)) in
    let defrt = list_mk_abs(newargs,defbod) in
    let expth = find (fun th -> lhand(concl th) = oldcon) defs in
    let rexpth = SUBS_CONV [expth] defrt in
    let deflf = mk_var(fst(dest_var oldcon),type_of defrt) in
    let defth = new_definition(mk_eq(deflf,rand(concl rexpth))) in
    TRANS defth (SYM rexpth) in

  (* ----------------------------------------------------------------------- *)
  (* Instantiate the induction theorem on the representatives to transfer    *)
  (* it to the new type(s). Uses "\x. rep-pred(x) /\ P(mk x)" for "P".       *)
  (* ----------------------------------------------------------------------- *)

  let instantiate_induction_theorem consindex ith =
    let avs,bod = strip_forall(concl ith) in
    let corlist = map((repeat rator F_F repeat rator) o dest_imp o body o rand)
      (conjuncts(rand bod)) in
    let consindex' = map (fun v -> let w = rev_assoc v corlist in
                                   w,assoc w consindex) avs in
    let recty = (hd o snd o dest_type o type_of o fst o snd o hd) consindex in
    let newtys = map (hd o snd o dest_type o type_of o snd o snd) consindex' in
    let ptypes = map (C mk_fun_ty bool_ty) newtys in
    let preds = make_args "P" [] ptypes in
    let args = make_args "x" [] (map (K recty) preds) in
    let lambs = map2 (fun (r,(m,d)) (p,a) ->
                       mk_abs(a,mk_conj(mk_comb(r,a),mk_comb(p,mk_comb(m,a)))))
                     consindex' (zip preds args) in
    SPECL lambs ith in

  (* ----------------------------------------------------------------------- *)
  (* Reduce a single clause of the postulated induction theorem (old_ver) ba *)
  (* to the kind wanted for the new type (new_ver); |- new_ver ==> old_ver   *)
  (* ----------------------------------------------------------------------- *)

  let pullback_induction_clause tybijpairs conthms =
    let PRERULE = GEN_REWRITE_RULE (funpow 3 RAND_CONV) (map SYM conthms) in
    let IPRULE = SYM o GEN_REWRITE_RULE I (map snd tybijpairs) in
    fun rthm tm ->
      let avs,bimp = strip_forall tm in
      if is_imp bimp then
        let ant,con = dest_imp bimp in
        let ths = map (CONV_RULE BETA_CONV) (CONJUNCTS (ASSUME ant)) in
        let tths,pths = unzip (map CONJ_PAIR ths) in
        let tth = MATCH_MP (SPEC_ALL rthm) (end_itlist CONJ tths) in
        let mths = map IPRULE (tth::tths) in
        let conth1 = BETA_CONV con in
        let contm1 = rand(concl conth1) in
        let conth2 = TRANS conth1
          (AP_TERM (rator contm1) (SUBS_CONV (tl mths) (rand contm1))) in
        let conth3 = PRERULE conth2 in
        let lctms = map concl pths in
        let asmin = mk_imp(list_mk_conj lctms,rand(rand(concl conth3))) in
        let argsin = map rand (conjuncts(lhand asmin)) in
        let argsgen =
          map (fun tm -> mk_var(fst(dest_var(rand tm)),type_of tm)) argsin in
        let asmgen = subst (zip argsgen argsin) asmin in
        let asmquant =
          list_mk_forall(snd(strip_comb(rand(rand asmgen))),asmgen) in
        let th1 = INST (zip argsin argsgen) (SPEC_ALL (ASSUME asmquant)) in
        let th2 = MP th1 (end_itlist CONJ pths) in
        let th3 = EQ_MP (SYM conth3) (CONJ tth th2) in
        DISCH asmquant (GENL avs (DISCH ant th3))
      else
        let con = bimp in
        let conth2 = BETA_CONV con in
        let tth = PART_MATCH I rthm (lhand(rand(concl conth2))) in
        let conth3 = PRERULE conth2 in
        let asmgen = rand(rand(concl conth3)) in
        let asmquant = list_mk_forall(snd(strip_comb(rand asmgen)),asmgen) in
        let th2 = SPEC_ALL (ASSUME asmquant) in
        let th3 = EQ_MP (SYM conth3) (CONJ tth th2) in
        DISCH asmquant (GENL avs th3) in

  (* ----------------------------------------------------------------------- *)
  (* Finish off a consequence of the induction theorem.                      *)
  (* ----------------------------------------------------------------------- *)

  let finish_induction_conclusion consindex tybijpairs =
    let tybij1,tybij2 = unzip tybijpairs in
    let PRERULE =
      GEN_REWRITE_RULE (LAND_CONV o LAND_CONV o RAND_CONV) tybij1 o
      GEN_REWRITE_RULE LAND_CONV tybij2
    and FINRULE = GEN_REWRITE_RULE RAND_CONV tybij1 in
    fun th ->
      let av,bimp = dest_forall(concl th) in
      let pv = lhand(body(rator(rand bimp))) in
      let p,v = dest_comb pv in
      let mk,dest = assoc p consindex in
      let ty = hd(snd(dest_type(type_of dest))) in
      let v' = mk_var(fst(dest_var v),ty) in
      let dv = mk_comb(dest,v') in
      let th1 = PRERULE (SPEC dv th) in
      let th2 = MP th1 (REFL (rand(lhand(concl th1)))) in
      let th3 = CONV_RULE BETA_CONV th2 in
      GEN v' (FINRULE (CONJUNCT2 th3)) in

  (* ----------------------------------------------------------------------- *)
  (* Derive the induction theorem.                                           *)
  (* ----------------------------------------------------------------------- *)

  let derive_induction_theorem consindex tybijpairs conthms iith rth =
    let bths = map2
      (pullback_induction_clause tybijpairs conthms)
      (CONJUNCTS rth) (conjuncts(lhand(concl iith))) in
    let asm = list_mk_conj(map (lhand o concl) bths) in
    let ths = map2 MP bths (CONJUNCTS (ASSUME asm)) in
    let th1 = MP iith (end_itlist CONJ ths) in
    let th2 = end_itlist CONJ (map
      (finish_induction_conclusion consindex tybijpairs) (CONJUNCTS th1)) in
    let th3 = DISCH asm th2 in
    let preds = map (rator o body o rand) (conjuncts(rand(concl th3))) in
    let th4 = GENL preds th3 in
    let pasms = filter (C mem (map fst consindex) o lhand) (hyp th4) in
    let th5 = itlist DISCH pasms th4 in
    let th6,_ = itlist SCRUB_EQUATION (hyp th5) (th5,[]) in
    let th7 = UNDISCH_ALL th6 in
    fst (itlist SCRUB_EQUATION (hyp th7) (th7,[])) in

  (* ----------------------------------------------------------------------- *)
  (* Create the recursive functions and eliminate pseudo-constructors.       *)
  (* (These are kept just long enough to derive the key property.)           *)
  (* ----------------------------------------------------------------------- *)

  let create_recursive_functions tybijpairs consindex conthms rth =
    let domtys = map (hd o snd o dest_type o type_of o snd o snd) consindex in
    let recty = (hd o snd o dest_type o type_of o fst o snd o hd) consindex in
    let ranty = mk_vartype "Z" in
    let fn = mk_var("fn",mk_fun_ty recty ranty)
    and fns = make_args "fn" [] (map (C mk_fun_ty ranty) domtys) in
    let args = make_args "a" [] domtys in
    let rights = map2 (fun (_,(_,d)) a -> mk_abs(a,mk_comb(fn,mk_comb(d,a))))
      consindex args in
    let eqs = map2 (curry mk_eq) fns rights in
    let fdefs = map ASSUME eqs in
    let fxths1 = map (fun th1 -> tryfind (fun th2 -> MK_COMB(th2,th1)) fdefs)
      conthms in
    let fxths2 = map (fun th -> TRANS th (BETA_CONV (rand(concl th)))) fxths1 in
    let mk_tybijcons (th1,th2) =
      let th3 = INST [rand(lhand(concl th1)),rand(lhand(concl th2))] th2 in
      let th4 = AP_TERM (rator(lhand(rand(concl th2)))) th1 in
      EQ_MP (SYM th3) th4 in
    let SCONV = GEN_REWRITE_CONV I (map mk_tybijcons tybijpairs)
    and ERULE = GEN_REWRITE_RULE I (map snd tybijpairs) in
    let simplify_fxthm rthm fxth =
      let pat = funpow 4 rand (concl fxth) in
      if is_imp(repeat (snd o dest_forall) (concl rthm)) then
        let th1 = PART_MATCH (rand o rand) rthm pat in
        let tms1 = conjuncts(lhand(concl th1)) in
        let ths2 = map (fun t -> EQ_MP (SYM(SCONV t)) TRUTH) tms1 in
        ERULE (MP th1 (end_itlist CONJ ths2))
      else
        ERULE (PART_MATCH rand rthm pat) in
    let fxths3 = map2 simplify_fxthm (CONJUNCTS rth) fxths2 in
    let fxths4 = map2 (fun th1 -> TRANS th1 o AP_TERM fn) fxths2 fxths3 in
    let cleanup_fxthm cth fxth =
      let tms = snd(strip_comb(rand(rand(concl fxth)))) in
      let kth = RIGHT_BETAS tms (ASSUME (hd(hyp cth))) in
      TRANS fxth (AP_TERM fn kth) in
    let fxth5 = end_itlist CONJ (map2 cleanup_fxthm conthms fxths4) in
    let pasms = filter (C mem (map fst consindex) o lhand) (hyp fxth5) in
    let fxth6 = itlist DISCH pasms fxth5 in
    let fxth7,_ =
      itlist SCRUB_EQUATION (itlist (union o hyp) conthms []) (fxth6,[]) in
    let fxth8 = UNDISCH_ALL fxth7 in
    fst (itlist SCRUB_EQUATION (subtract (hyp fxth8) eqs) (fxth8,[])) in

  (* ----------------------------------------------------------------------- *)
  (* Create a function for recursion clause.                                 *)
  (* ----------------------------------------------------------------------- *)

  let create_recursion_iso_constructor =
    let s = `s:num->Z` in
    let zty = `:Z` in
    let numty = `:num` in
    let rec extract_arg tup v =
      if v = tup then REFL tup else
      let t1,t2 = dest_pair tup in
      let PAIR_th = ISPECL [t1;t2] (if free_in v t1 then FST else SND) in
      let tup' = rand(concl PAIR_th) in
      if tup' = v then PAIR_th else
      let th = extract_arg (rand(concl PAIR_th)) v in
      SUBS[SYM PAIR_th] th in
    fun consindex ->
      let recty = hd(snd(dest_type(type_of(fst(hd consindex))))) in
      let domty = hd(snd(dest_type recty)) in
      let i = mk_var("i",domty)
      and r = mk_var("r",mk_fun_ty numty recty) in
      let mks = map (fst o snd) consindex in
      let mkindex = map (fun t -> hd(tl(snd(dest_type(type_of t)))),t) mks in
      fun cth ->
        let artms = snd(strip_comb(rand(rand(concl cth)))) in
        let artys = mapfilter (type_of o rand) artms in
        let args,bod = strip_abs(rand(hd(hyp cth))) in
        let ccitm,rtm = dest_comb bod in
        let cctm,itm = dest_comb ccitm in
        let rargs,iargs = partition (C free_in rtm) args in
        let xths = map (extract_arg itm) iargs in
        let cargs' = map (subst [i,itm] o lhand o concl) xths in
        let indices = map sucivate (0--(length rargs - 1)) in
        let rindexed = map (curry mk_comb r) indices in
        let rargs' = map2 (fun a rx -> mk_comb(assoc a mkindex,rx))
            artys rindexed in
        let sargs' = map (curry mk_comb s) indices in
        let allargs = cargs'@ rargs' @ sargs' in
        let funty = itlist (mk_fun_ty o type_of) allargs zty in
        let funname = fst(dest_const(repeat rator (lhand(concl cth))))^"'" in
        let funarg = mk_var(funname,funty) in
        list_mk_abs([i;r;s],list_mk_comb(funarg,allargs)) in

  (* ----------------------------------------------------------------------- *)
  (* Derive the recursion theorem.                                           *)
  (* ----------------------------------------------------------------------- *)

  let derive_recursion_theorem =
    let CCONV = funpow 3 RATOR_CONV (REPEATC (GEN_REWRITE_CONV I [FCONS])) in
    fun tybijpairs consindex conthms rath ->
      let isocons = map (create_recursion_iso_constructor consindex) conthms in
      let ty = type_of(hd isocons) in
      let fcons = mk_const("FCONS",[ty,aty])
      and fnil = mk_const("FNIL",[ty,aty]) in
      let bigfun = itlist (mk_binop fcons) isocons fnil in
      let eth = ISPEC bigfun CONSTR_REC in
      let fn = rator(rand(hd(conjuncts(concl rath)))) in
      let betm = let v,bod = dest_abs(rand(concl eth)) in vsubst[fn,v] bod in
      let LCONV = REWR_CONV (ASSUME betm) in
      let fnths =
        map (fun t -> RIGHT_BETAS [bndvar(rand t)] (ASSUME t)) (hyp rath) in
      let SIMPER = PURE_REWRITE_RULE
        (map SYM fnths @ map fst tybijpairs @ [FST; SND; FCONS; BETA_THM]) in
      let hackdown_rath th =
        let ltm,rtm = dest_eq(concl th) in
        let wargs = snd(strip_comb(rand ltm)) in
        let th1 = TRANS th (LCONV rtm) in
        let th2 = TRANS th1 (CCONV (rand(concl th1))) in
        let th3 = TRANS th2 (funpow 2 RATOR_CONV BETA_CONV (rand(concl th2))) in
        let th4 = TRANS th3 (RATOR_CONV BETA_CONV (rand(concl th3))) in
        let th5 = TRANS th4 (BETA_CONV (rand(concl th4))) in
        GENL wargs (SIMPER th5) in
      let rthm = end_itlist CONJ (map hackdown_rath (CONJUNCTS rath)) in
      let seqs =
        let unseqs = filter is_eq (hyp rthm) in
        let tys = map (hd o snd o dest_type o type_of o snd o snd) consindex in
        map (fun ty -> find
          (fun t -> hd(snd(dest_type(type_of(lhand t)))) = ty) unseqs) tys in
      let rethm = itlist EXISTS_EQUATION seqs rthm in
      let fethm = CHOOSE(fn,eth) rethm in
      let pcons = map (repeat rator o rand o repeat (snd o dest_forall))
        (conjuncts(concl rthm)) in
      GENL pcons fethm in

  (* ----------------------------------------------------------------------- *)
  (* Basic function: returns induction and recursion separately. No parser.  *)
  (* ----------------------------------------------------------------------- *)

  fun def ->
    let defs,rth,ith = justify_inductive_type_model def in
    let neths = prove_model_inhabitation rth in
    let tybijpairs = map (define_inductive_type defs) neths in
    let preds = map (repeat rator o concl) neths in
    let mkdests = map
      (fun (th,_) -> let tm = lhand(concl th) in rator tm,rator(rand tm))
      tybijpairs in
    let consindex = zip preds mkdests in
    let condefs = map (define_inductive_type_constructor defs consindex)
                      (CONJUNCTS rth) in
    let conthms = map
      (fun th -> let args = fst(strip_abs(rand(concl th))) in
                 RIGHT_BETAS args th) condefs in
    let iith = instantiate_induction_theorem consindex ith in
    let fth = derive_induction_theorem consindex tybijpairs conthms iith rth in
    let rath = create_recursive_functions tybijpairs consindex conthms rth in
    let kth = derive_recursion_theorem tybijpairs consindex conthms rath in
    fth,kth;;

(* ------------------------------------------------------------------------- *)
(* Parser to present a nice interface a la Melham.                           *)
(* ------------------------------------------------------------------------- *)

let parse_inductive_type_specification =
  let parse_type_loc src =
    let pty,rst = parse_pretype src in
    type_of_pretype pty,rst in
  let parse_type_conapp src =
    let cn,sps =
     match src with (Ident cn)::sps -> cn,sps
                  | _ -> fail() in
    let tys,rst = many parse_type_loc sps in
    (cn,tys),rst in
  let parse_type_clause src =
    let tn,sps =
      match src with (Ident tn)::sps -> tn,sps
                   | _ -> fail() in
    let tys,rst = (a (Ident "=") ++ listof parse_type_conapp (a (Resword "|"))
                                   "type definition clauses"
                   >> snd) sps in
    (mk_vartype tn,tys),rst in
  let parse_type_definition =
    listof parse_type_clause (a (Resword ";")) "type definition" in
  fun s ->
    let spec,rst = (parse_type_definition o lex o explode) s in
    if rst = [] then spec
    else failwith "parse_inductive_type_specification: junk after def";;

(* ------------------------------------------------------------------------- *)
(* Use this temporary version to define the sum type.                        *)
(* ------------------------------------------------------------------------- *)

let sum_INDUCT,sum_RECURSION =
  define_type_raw (parse_inductive_type_specification "sum = INL A | INR B");;

let OUTL = new_recursive_definition sum_RECURSION
  `OUTL (INL x :A+B) = x`;;

let OUTR = new_recursive_definition sum_RECURSION
  `OUTR (INR y :A+B) = y`;;

(* ------------------------------------------------------------------------- *)
(* Generalize the recursion theorem to multiple domain types.                *)
(* (We needed to use a single type to justify it via a proforma theorem.)    *)
(*                                                                           *)
(* NB! Before this is called nontrivially (i.e. more than one new type)      *)
(*     the type constructor ":sum", used internally, must have been defined. *)
(* ------------------------------------------------------------------------- *)

let define_type_raw =
  let generalize_recursion_theorem =
    let ELIM_OUTCOMBS = GEN_REWRITE_RULE TOP_DEPTH_CONV [OUTL; OUTR] in
    let rec mk_sum tys =
      let k = length tys in
      if k = 1 then hd tys else
      let tys1,tys2 = chop_list (k / 2) tys in
      mk_type("sum",[mk_sum tys1; mk_sum tys2]) in
    let mk_inls =
      let rec mk_inls ty =
        if is_vartype ty then [mk_var("x",ty)] else
        let _,[ty1;ty2] = dest_type ty in
        let inls1 = mk_inls ty1
        and inls2 = mk_inls ty2 in
        let inl = mk_const("INL",[ty1,aty; ty2,bty])
        and inr = mk_const("INR",[ty1,aty; ty2,bty]) in
        map (curry mk_comb inl) inls1 @ map (curry mk_comb inr) inls2 in
      fun ty -> let bods = mk_inls ty in
                map (fun t -> mk_abs(find_term is_var t,t)) bods in
    let mk_outls =
      let rec mk_inls sof ty =
        if is_vartype ty then [sof] else
        let _,[ty1;ty2] = dest_type ty in
        let outl = mk_const("OUTL",[ty1,aty; ty2,bty])
        and outr = mk_const("OUTR",[ty1,aty; ty2,bty]) in
        mk_inls (mk_comb(outl,sof)) ty1 @ mk_inls (mk_comb(outr,sof)) ty2 in
      fun ty -> let x = mk_var("x",ty) in
                map (curry mk_abs x) (mk_inls x ty) in
    let mk_newfun fn outl =
      let s,ty = dest_var fn in
      let dty = hd(snd(dest_type ty)) in
      let x = mk_var("x",dty) in
      let y,bod = dest_abs outl in
      let r = mk_abs(x,vsubst[mk_comb(fn,x),y] bod) in
      let l = mk_var(s,type_of r) in
      let th1 = ASSUME (mk_eq(l,r)) in
      RIGHT_BETAS [x] th1 in
    fun th ->
      let avs,ebod = strip_forall(concl th) in
      let evs,bod = strip_exists ebod in
      let n = length evs in
      if n = 1 then th else
      let tys = map (fun i -> mk_vartype ("Z"^(string_of_int i)))
                    (0--(n - 1)) in
      let sty = mk_sum tys in
      let inls = mk_inls sty
      and outls = mk_outls sty in
      let zty = type_of(rand(snd(strip_forall(hd(conjuncts bod))))) in
      let ith = INST_TYPE [sty,zty] th in
      let avs,ebod = strip_forall(concl ith) in
      let evs,bod = strip_exists ebod in
      let fns' = map2 mk_newfun evs outls in
      let fnalist = zip evs (map (rator o lhs o concl) fns')
      and inlalist = zip evs inls
      and outlalist = zip evs outls in
      let hack_clause tm =
        let avs,bod = strip_forall tm in
        let l,r = dest_eq bod in
        let fn,args = strip_comb r in
        let pargs = map
          (fun a -> let g = genvar(type_of a) in
                    if is_var a then g,g else
                    let outl = assoc (rator a) outlalist in
                    mk_comb(outl,g),g) args in
        let args',args'' = unzip pargs in
        let inl = assoc (rator l) inlalist in
        let rty = hd(snd(dest_type(type_of inl))) in
        let nty = itlist (mk_fun_ty o type_of) args' rty in
        let fn' = mk_var(fst(dest_var fn),nty) in
        let r' = list_mk_abs(args'',mk_comb(inl,list_mk_comb(fn',args'))) in
        r',fn in
      let defs = map hack_clause (conjuncts bod) in
      let jth = BETA_RULE (SPECL (map fst defs) ith) in
      let bth = ASSUME (snd(strip_exists(concl jth))) in
      let finish_clause th =
        let avs,bod = strip_forall (concl th) in
        let outl = assoc (rator (lhand bod)) outlalist in
        GENL avs (BETA_RULE (AP_TERM outl (SPECL avs th))) in
      let cth = end_itlist CONJ (map finish_clause (CONJUNCTS bth)) in
      let dth = ELIM_OUTCOMBS cth in
      let eth = GEN_REWRITE_RULE ONCE_DEPTH_CONV (map SYM fns') dth in
      let fth = itlist SIMPLE_EXISTS (map snd fnalist) eth in
      let dtms = map (hd o hyp) fns' in
      let gth = itlist (fun e th -> let l,r = dest_eq e in
                        MP (INST [r,l] (DISCH e th)) (REFL r)) dtms fth in
      let hth = PROVE_HYP jth (itlist SIMPLE_CHOOSE evs gth) in
      let xvs = map (fst o strip_comb o rand o snd o strip_forall)
                    (conjuncts(concl eth)) in
      GENL xvs hth in
  fun def -> let ith,rth = define_type_raw def in
             ith,generalize_recursion_theorem rth;;

(* ------------------------------------------------------------------------- *)
(* Set up options and lists.                                                 *)
(* ------------------------------------------------------------------------- *)

let option_INDUCT,option_RECURSION =
  define_type_raw
   (parse_inductive_type_specification "option = NONE | SOME A");;

let list_INDUCT,list_RECURSION =
  define_type_raw
   (parse_inductive_type_specification "list = NIL | CONS A list");;

let FORALL_OPTION_THM = prove
 (`!P:A option->bool. (!x. P x) <=> P NONE /\ !a. P(SOME a)`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[option_INDUCT] THEN SIMP_TAC[]);;

let EXISTS_OPTION_THM = prove
 (`!P:A option->bool. (?x. P x) <=> P NONE \/ ?a. P(SOME a)`,
  GEN_TAC THEN REWRITE_TAC[MESON[] `(?x. P x) <=> ~(!x. ~P x)`] THEN
  REWRITE_TAC[FORALL_OPTION_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Tools for proving injectivity and distinctness of constructors.           *)
(* ------------------------------------------------------------------------- *)

let prove_constructors_injective =
  let DEPAIR = GEN_REWRITE_RULE TOP_SWEEP_CONV [PAIR_EQ] in
  let prove_distinctness ax pat =
    let f,args = strip_comb pat in
    let rt = end_itlist (curry mk_pair) args in
    let ty = mk_fun_ty (type_of pat) (type_of rt) in
    let fn = genvar ty in
    let dtm = mk_eq(mk_comb(fn,pat),rt) in
    let eth = prove_recursive_functions_exist ax (list_mk_forall(args,dtm)) in
    let args' = variants args args in
    let atm = mk_eq(pat,list_mk_comb(f,args')) in
    let ath = ASSUME atm in
    let bth = AP_TERM fn ath in
    let cth1 = SPECL args (ASSUME(snd(dest_exists(concl eth)))) in
    let cth2 = INST (zip args' args) cth1 in
    let pth = TRANS (TRANS (SYM cth1) bth) cth2 in
    let qth = DEPAIR pth in
    let qtm = concl qth in
    let rth = rev_itlist (C(curry MK_COMB)) (CONJUNCTS(ASSUME qtm)) (REFL f) in
    let tth = IMP_ANTISYM_RULE (DISCH atm qth) (DISCH qtm rth) in
    let uth = GENL args (GENL args' tth) in
    PROVE_HYP eth (SIMPLE_CHOOSE fn uth) in
  fun ax ->
    let cls = conjuncts(snd(strip_exists(snd(strip_forall(concl ax))))) in
    let pats = map (rand o lhand o snd o strip_forall) cls in
    end_itlist CONJ (mapfilter (prove_distinctness ax) pats);;

let prove_constructors_distinct =
  let num_ty = `:num` in
  let rec allopairs f l m =
    if l = [] then [] else
    map (f (hd l)) (tl m) @ allopairs f (tl l) (tl m) in
  let NEGATE = GEN_ALL o CONV_RULE (REWR_CONV (TAUT `a ==> F <=> ~a`)) in
  let prove_distinct ax pat =
    let nums = map mk_small_numeral (0--(length pat - 1)) in
    let fn = genvar (mk_type("fun",[type_of(hd pat); num_ty])) in
    let ls = map (curry mk_comb fn) pat in
    let defs = map2 (fun l r -> list_mk_forall(frees (rand l),mk_eq(l,r)))
      ls nums in
    let eth = prove_recursive_functions_exist ax (list_mk_conj defs) in
    let ev,bod = dest_exists(concl eth) in
    let REWRITE = GEN_REWRITE_RULE ONCE_DEPTH_CONV (CONJUNCTS (ASSUME bod)) in
    let pat' = map
     (fun t -> let f,args = if is_numeral t then t,[] else strip_comb t in
               list_mk_comb(f,variants args args)) pat in
    let pairs = allopairs (curry mk_eq) pat pat' in
    let nths = map (REWRITE o AP_TERM fn o ASSUME) pairs in
    let fths = map2 (fun t th -> NEGATE (DISCH t (CONV_RULE NUM_EQ_CONV th)))
      pairs nths in
    CONJUNCTS(PROVE_HYP eth (SIMPLE_CHOOSE ev (end_itlist CONJ fths))) in
  fun ax ->
    let cls = conjuncts(snd(strip_exists(snd(strip_forall(concl ax))))) in
    let lefts = map (dest_comb o lhand o snd o strip_forall) cls in
    let fns = itlist (insert o fst) lefts [] in
    let pats = map (fun f -> map snd (filter ((=)f o fst) lefts)) fns in
    end_itlist CONJ
     (end_itlist (@) (mapfilter (prove_distinct ax) pats));;

(* ------------------------------------------------------------------------- *)
(* Automatically prove the case analysis theorems.                           *)
(* ------------------------------------------------------------------------- *)

let prove_cases_thm =
  let mk_exclauses x rpats =
    let xts = map (fun t -> list_mk_exists(frees t,mk_eq(x,t))) rpats in
    mk_abs(x,list_mk_disj xts) in
  let prove_triv tm =
    let evs,bod = strip_exists tm in
    let l,r = dest_eq bod in
    if l = r then REFL l else
    let lf,largs = strip_comb l
    and rf,rargs = strip_comb r in
    if lf = rf then
      let ths = map (ASSUME o mk_eq) (zip rargs largs) in
      let th1 = rev_itlist (C (curry MK_COMB)) ths (REFL lf) in
      itlist EXISTS_EQUATION (map concl ths) (SYM th1)
    else failwith "prove_triv" in
  let rec prove_disj tm =
    if is_disj tm then
      let l,r = dest_disj tm in
      try DISJ1 (prove_triv l) r
      with Failure _ -> DISJ2 l (prove_disj r)
    else
      prove_triv tm in
  let prove_eclause tm =
    let avs,bod = strip_forall tm in
    let ctm = if is_imp bod then rand bod else bod in
    let cth = prove_disj ctm in
    let dth = if is_imp bod then DISCH (lhand bod) cth else cth in
    GENL avs dth in
  fun th ->
    let avs,bod = strip_forall(concl th) in
    let cls = map (snd o strip_forall) (conjuncts(lhand bod)) in
    let pats = map (fun t -> if is_imp t then rand t else t) cls in
    let spats = map dest_comb pats in
    let preds = itlist (insert o fst) spats [] in
    let rpatlist = map
      (fun pr -> map snd (filter (fun (p,x) -> p = pr) spats)) preds in
    let xs = make_args "x" (freesl pats) (map (type_of o hd) rpatlist) in
    let xpreds = map2 mk_exclauses xs rpatlist in
    let ith = BETA_RULE (INST (zip xpreds preds) (SPEC_ALL th)) in
    let eclauses = conjuncts(fst(dest_imp(concl ith))) in
    MP ith (end_itlist CONJ (map prove_eclause eclauses));;

(* ------------------------------------------------------------------------- *)
(* Now deal with nested recursion. Need a store of previous theorems.        *)
(* ------------------------------------------------------------------------- *)

inductive_type_store :=
 ["list",(2,list_INDUCT,list_RECURSION);
  "option",(2,option_INDUCT,option_RECURSION);
  "sum",(2,sum_INDUCT,sum_RECURSION)] @
 (!inductive_type_store);;

(* ------------------------------------------------------------------------- *)
(* Also add a cached rewrite of distinctness and injectivity theorems. Since *)
(* there can be quadratically many distinctness clauses, it would really be  *)
(* preferable to have a conversion, but this seems OK up 100 constructors.   *)
(* ------------------------------------------------------------------------- *)

let basic_rectype_net = ref empty_net;;
let distinctness_store = ref ["bool",TAUT `(T <=> F) <=> F`];;
let injectivity_store = ref [];;

let extend_rectype_net (tyname,(_,_,rth)) =
  let ths1 = try [prove_constructors_distinct rth] with Failure _ -> []
  and ths2 = try [prove_constructors_injective rth] with Failure _ -> [] in
  let canon_thl = itlist (mk_rewrites false) (ths1 @ ths2) [] in
  distinctness_store := map (fun th -> tyname,th) ths1 @ (!distinctness_store);
  injectivity_store := map (fun th -> tyname,th) ths2 @ (!injectivity_store);
  basic_rectype_net :=
    itlist (net_of_thm true) canon_thl (!basic_rectype_net);;

do_list extend_rectype_net (!inductive_type_store);;

(* ------------------------------------------------------------------------- *)
(* Return distinctness and injectivity for a type by simple lookup.          *)
(* ------------------------------------------------------------------------- *)

let distinctness ty = assoc ty (!distinctness_store);;

let injectivity ty = assoc ty (!injectivity_store);;

let cases ty =
  if ty = "num" then num_CASES else
  let _,ith,_ = assoc ty (!inductive_type_store) in prove_cases_thm ith;;

let option_DISTINCT = prove
 (`!a:A. ~(SOME a = NONE)`,
  REWRITE_TAC[distinctness "option"]);;

let option_INJ = prove
 (`!a b:A. SOME a = SOME b <=> a = b`,
  REWRITE_TAC[injectivity "option"]);;

(* ------------------------------------------------------------------------- *)
(* Convenient definitions for type isomorphism.                              *)
(* ------------------------------------------------------------------------- *)

let ISO = new_definition
  `ISO (f:A->B) (g:B->A) <=> (!x. f(g x) = x) /\ (!y. g(f y) = y)`;;

let ISO_REFL = prove
 (`ISO (\x:A. x) (\x. x)`,
  REWRITE_TAC[ISO]);;

let ISO_FUN = prove
 (`ISO (f:A->A') f' /\ ISO (g:B->B') g'
   ==> ISO (\h a'. g(h(f' a'))) (\h a. g'(h(f a)))`,
  REWRITE_TAC[ISO; FUN_EQ_THM] THEN MESON_TAC[]);;

let ISO_USAGE = prove
 (`ISO f g
   ==> (!P. (!x. P x) <=> (!x. P(g x))) /\
       (!P. (?x. P x) <=> (?x. P(g x))) /\
       (!(a:A) (b:B). (a = g b) <=> (f a = b))`,
  REWRITE_TAC[ISO; FUN_EQ_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hence extend type definition to nested types.                             *)
(* ------------------------------------------------------------------------- *)

let define_type_raw =

  (* ----------------------------------------------------------------------- *)
  (* Dispose of trivial antecedent.                                          *)
  (* ----------------------------------------------------------------------- *)

  let TRIV_ANTE_RULE =
    let TRIV_IMP_CONV tm =
      let avs,bod = strip_forall tm in
      let bth =
        if is_eq bod then REFL (rand bod) else
        let ant,con = dest_imp bod in
        let ith = SUBS_CONV (CONJUNCTS(ASSUME ant)) (lhs con) in
        DISCH ant ith in
      GENL avs bth in
    fun th ->
      let tm = concl th in
      if is_imp tm then
        let ant,con = dest_imp(concl th) in
        let cjs = conjuncts ant in
        let cths = map TRIV_IMP_CONV cjs in
        MP th (end_itlist CONJ cths)
      else th in

  (* ----------------------------------------------------------------------- *)
  (* Lift type bijections to "arbitrary" (well, free rec or function) type.  *)
  (* ----------------------------------------------------------------------- *)

  let ISO_EXPAND_CONV = PURE_ONCE_REWRITE_CONV[ISO] in

  let rec lift_type_bijections iths cty =
    let itys = map (hd o snd o dest_type o type_of o lhand o concl) iths in
    try assoc cty (zip itys iths) with Failure _ ->
    if not (exists (C occurs_in cty) itys)
    then INST_TYPE [cty,aty] ISO_REFL else
    let tycon,isotys = dest_type cty in
    if tycon = "fun"
    then MATCH_MP ISO_FUN
           (end_itlist CONJ (map (lift_type_bijections iths) isotys))
    else failwith
            ("lift_type_bijections: Unexpected type operator \""^tycon^"\"") in

  (* ----------------------------------------------------------------------- *)
  (* Prove isomorphism of nested types where former is the smaller.          *)
  (* ----------------------------------------------------------------------- *)

  let DE_EXISTENTIALIZE_RULE =
    let pth = prove
     (`(?) P ==> (c = (@)P) ==> P c`,
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
      DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC SELECT_AX THEN POP_ASSUM ACCEPT_TAC) in
    let USE_PTH = MATCH_MP pth in
    let rec DE_EXISTENTIALIZE_RULE th =
      if not (is_exists(concl th)) then [],th else
      let th1 = USE_PTH th in
      let v1 = rand(rand(concl th1)) in
      let gv = genvar(type_of v1) in
      let th2 = CONV_RULE BETA_CONV (UNDISCH (INST [gv,v1] th1)) in
      let vs,th3 = DE_EXISTENTIALIZE_RULE th2 in
      gv::vs,th3 in
    DE_EXISTENTIALIZE_RULE in

  let grab_type = type_of o rand o lhand o snd o strip_forall in

  let clause_corresponds cl0  =
    let f0,ctm0 = dest_comb (lhs cl0) in
    let c0 = fst(dest_const(fst(strip_comb ctm0))) in
    let dty0,rty0 = dest_fun_ty (type_of f0) in
    fun cl1 ->
      let f1,ctm1 = dest_comb (lhs cl1) in
      let c1 = fst(dest_const(fst(strip_comb ctm1))) in
      let dty1,rty1 = dest_fun_ty (type_of f1) in
      c0 = c1 && dty0 = rty1 && rty0 = dty1 in

  let prove_inductive_types_isomorphic n k (ith0,rth0) (ith1,rth1) =
    let sth0 = SPEC_ALL rth0
    and sth1 = SPEC_ALL rth1
    and t_tm = concl TRUTH in
    let pevs0,pbod0 = strip_exists (concl sth0)
    and pevs1,pbod1 = strip_exists (concl sth1) in
    let pcjs0,qcjs0 = chop_list k (conjuncts pbod0)
    and pcjs1,qcjs1 = chop_list k (snd(chop_list n (conjuncts pbod1))) in
    let tyal0 = setify (zip (map grab_type pcjs1) (map grab_type pcjs0)) in
    let tyal1 = map (fun (a,b) -> (b,a)) tyal0 in
    let tyins0 = map
     (fun f -> let domty,ranty = dest_fun_ty (type_of f) in
               tysubst tyal0 domty,ranty) pevs0
    and tyins1 = map
     (fun f -> let domty,ranty = dest_fun_ty (type_of f) in
               tysubst tyal1 domty,ranty) pevs1 in
    let tth0 = INST_TYPE tyins0 sth0
    and tth1 = INST_TYPE tyins1 sth1 in
    let evs0,bod0 = strip_exists(concl tth0)
    and evs1,bod1 = strip_exists(concl tth1) in
    let lcjs0,rcjs0 = chop_list k (map (snd o strip_forall) (conjuncts bod0))
    and lcjs1,rcjsx = chop_list k (map (snd o strip_forall)
      (snd(chop_list n (conjuncts bod1)))) in
    let rcjs1 =  map (fun t -> find (clause_corresponds t) rcjsx) rcjs0 in
    let proc_clause tm0 tm1 =
      let l0,r0 = dest_eq tm0
      and l1,r1 = dest_eq tm1 in
      let vc0,wargs0 = strip_comb r0 in
      let con0,vargs0 = strip_comb(rand l0) in
      let gargs0 = map (genvar o type_of) wargs0 in
      let nestf0 = map (fun a -> can (find (fun t -> is_comb t && rand t = a))
        wargs0) vargs0 in
      let targs0 = map2 (fun a f ->
        if f then find (fun t -> is_comb t && rand t = a) wargs0 else a)
         vargs0 nestf0 in
      let gvlist0 = zip wargs0 gargs0 in
      let xargs = map (fun v -> assoc v gvlist0) targs0 in
      let inst0 =
        list_mk_abs(gargs0,list_mk_comb(fst(strip_comb(rand l1)),xargs)),vc0 in
      let vc1,wargs1 = strip_comb r1 in
      let con1,vargs1 = strip_comb(rand l1) in
      let gargs1 = map (genvar o type_of) wargs1 in
      let targs1 = map2
        (fun a f -> if f then
                    find (fun t -> is_comb t && rand t = a) wargs1
                    else a) vargs1 nestf0 in
      let gvlist1 = zip wargs1 gargs1 in
      let xargs = map (fun v -> assoc v gvlist1) targs1 in
      let inst1 =
        list_mk_abs(gargs1,list_mk_comb(fst(strip_comb(rand l0)),xargs)),vc1 in
      inst0,inst1 in
    let insts0,insts1 = unzip (map2 proc_clause (lcjs0@rcjs0) (lcjs1@rcjs1)) in
    let uth0 = BETA_RULE(INST insts0 tth0)
    and uth1 = BETA_RULE(INST insts1 tth1) in
    let efvs0,sth0 = DE_EXISTENTIALIZE_RULE uth0
    and efvs1,sth1 = DE_EXISTENTIALIZE_RULE uth1 in
    let efvs2 = map
     (fun t1 -> find (fun t2 -> hd(tl(snd(dest_type(type_of t1)))) =
                                hd(snd(dest_type(type_of t2)))) efvs1) efvs0 in
    let isotms = map2 (fun ff gg -> list_mk_icomb "ISO" [ff;gg]) efvs0 efvs2 in
    let ctm = list_mk_conj isotms in
    let cth1 = ISO_EXPAND_CONV ctm in
    let ctm1 = rand(concl cth1) in
    let cjs = conjuncts ctm1 in
    let eee = map (fun n -> n mod 2 = 0) (0--(length cjs - 1)) in
    let cjs1,cjs2 = partition fst (zip eee cjs) in
    let ctm2 = mk_conj(list_mk_conj (map snd cjs1),
                       list_mk_conj (map snd cjs2)) in
    let DETRIV_RULE = TRIV_ANTE_RULE o REWRITE_RULE[sth0;sth1] in
    let jth0 =
      let itha = SPEC_ALL ith0 in
      let icjs = conjuncts(rand(concl itha)) in
      let cinsts = map
        (fun tm -> tryfind (fun vtm -> term_match [] vtm tm) icjs)
        (conjuncts (rand ctm2)) in
      let tvs = subtract (fst(strip_forall(concl ith0)))
                  (itlist (fun (_,x,_) -> union (map snd x)) cinsts []) in
      let ctvs =
        map (fun p -> let x = mk_var("x",hd(snd(dest_type(type_of p)))) in
                             mk_abs(x,t_tm),p) tvs in
      DETRIV_RULE (INST ctvs (itlist INSTANTIATE cinsts itha))
    and jth1 =
      let itha = SPEC_ALL ith1 in
      let icjs = conjuncts(rand(concl itha)) in
      let cinsts = map
        (fun tm -> tryfind (fun vtm -> term_match [] vtm tm) icjs)
        (conjuncts (lhand ctm2)) in
      let tvs = subtract (fst(strip_forall(concl ith1)))
                    (itlist (fun (_,x,_) -> union (map snd x)) cinsts []) in
      let ctvs =
        map (fun p -> let x = mk_var("x",hd(snd(dest_type(type_of p)))) in
                               mk_abs(x,t_tm),p) tvs in
      DETRIV_RULE (INST ctvs (itlist INSTANTIATE cinsts itha)) in
    let cths4 = map2 CONJ (CONJUNCTS jth0) (CONJUNCTS jth1) in
    let cths5 = map (PURE_ONCE_REWRITE_RULE[GSYM ISO]) cths4 in
    let cth6 = end_itlist CONJ cths5 in
    cth6,CONJ sth0 sth1 in

  (* ----------------------------------------------------------------------- *)
  (* Define nested type by doing a 1-level unwinding.                        *)
  (* ----------------------------------------------------------------------- *)

  let SCRUB_ASSUMPTION th =
    let hyps = hyp th in
    let eqn = find (fun t -> let x = lhs t in
                             forall (fun u -> not (free_in x (rand u))) hyps)
                   hyps in
    let l,r = dest_eq eqn in
    MP (INST [r,l] (DISCH eqn th)) (REFL r) in

  let define_type_basecase def =
    let add_id s = fst(dest_var(genvar bool_ty)) in
    let def' = map (I F_F (map (add_id F_F I))) def in
    define_type_raw def' in

  let SIMPLE_BETA_RULE = GSYM o PURE_REWRITE_RULE[BETA_THM; FUN_EQ_THM] in
  let ISO_USAGE_RULE = MATCH_MP ISO_USAGE in
  let SIMPLE_ISO_EXPAND_RULE = CONV_RULE(REWR_CONV ISO) in

  let REWRITE_FUN_EQ_RULE =
    let ths = itlist (mk_rewrites false) [FUN_EQ_THM] [] in
    let net = itlist (net_of_thm false) ths (basic_net()) in
    CONV_RULE o GENERAL_REWRITE_CONV true TOP_DEPTH_CONV net in

  let is_nested vs ty =
    not (is_vartype ty) && not (intersect (tyvars ty) vs = []) in
  let rec modify_type alist ty =
    try rev_assoc ty alist
    with Failure _ -> try
        let tycon,tyargs = dest_type ty in
        mk_type(tycon,map (modify_type alist) tyargs)
    with Failure _ -> ty in
  let modify_item alist (s,l) =
    s,map (modify_type alist) l in
  let modify_clause alist (l,lis) =
     l,map (modify_item alist) lis in
  let recover_clause id tm =
    let con,args = strip_comb tm in
    fst(dest_const con)^id,map type_of args in
  let rec create_auxiliary_clauses nty =
    let id = fst(dest_var(genvar bool_ty)) in
    let tycon,tyargs = dest_type nty in
    let k,ith,rth = try assoc tycon (!inductive_type_store) with Failure _ ->
      failwith ("Can't find definition for nested type: "^tycon) in
    let evs,bod = strip_exists(snd(strip_forall(concl rth))) in
    let cjs = map (lhand o snd o strip_forall) (conjuncts bod) in
    let rtys = map (hd o snd o dest_type o type_of) evs in
    let tyins = tryfind (fun vty -> type_match vty nty []) rtys in
    let cjs' = map (inst tyins o rand) (fst(chop_list k cjs)) in
    let mtys = itlist (insert o type_of) cjs' [] in
    let pcons = map (fun ty -> filter (fun t -> type_of t = ty) cjs') mtys in
    let cls' = zip mtys (map (map (recover_clause id)) pcons) in
    let tyal = map (fun ty -> mk_vartype(fst(dest_type ty)^id),ty) mtys in
    let cls'' = map (modify_type tyal F_F map (modify_item tyal)) cls' in
    k,tyal,cls'',INST_TYPE tyins ith,INST_TYPE tyins rth in
  let rec define_type_nested def =
    let n = length(itlist (@) (map (map fst o snd) def) []) in
    let newtys = map fst def in
    let utys = unions (itlist (union o map snd o snd) def []) in
    let rectys = filter (is_nested newtys) utys in
    if rectys = [] then
      let th1,th2 = define_type_basecase def in n,th1,th2 else
    let nty = hd (sort (fun t1 t2 -> occurs_in t2 t1) rectys) in
    let k,tyal,ncls,ith,rth = create_auxiliary_clauses nty in
    let cls = map (modify_clause tyal) def @ ncls in
    let _,ith1,rth1 = define_type_nested cls in
    let xnewtys = map (hd o snd o dest_type o type_of)
                      (fst(strip_exists(snd(strip_forall(concl rth1))))) in
    let xtyal = map (fun ty -> let s = dest_vartype ty in
                               find (fun t -> fst(dest_type t) = s) xnewtys,ty)
                    (map fst cls) in
    let ith0 = INST_TYPE xtyal ith
    and rth0 = INST_TYPE xtyal rth in
    let isoth,rclauses =
      prove_inductive_types_isomorphic n k (ith0,rth0) (ith1,rth1) in
    let irth3 = CONJ ith1 rth1 in
    let vtylist = itlist (insert o type_of) (variables(concl irth3)) [] in
    let isoths = CONJUNCTS isoth in
    let isotys = map (hd o snd o dest_type o type_of o lhand o concl) isoths in
    let ctylist = filter
      (fun ty -> exists (fun t -> occurs_in t ty) isotys) vtylist in
    let atylist = itlist
      (union o striplist dest_fun_ty) ctylist [] in
    let isoths' = map (lift_type_bijections isoths)
      (filter (fun ty -> exists (fun t -> occurs_in t ty) isotys) atylist) in
    let cisoths = map (BETA_RULE o lift_type_bijections isoths')
      ctylist in
    let uisoths = map ISO_USAGE_RULE cisoths in
    let visoths = map (ASSUME o concl) uisoths in
    let irth4 = itlist PROVE_HYP uisoths (REWRITE_FUN_EQ_RULE visoths irth3) in
    let irth5 = REWRITE_RULE
      (rclauses :: map SIMPLE_ISO_EXPAND_RULE isoths') irth4 in
    let irth6 = repeat SCRUB_ASSUMPTION irth5 in
    let ncjs = filter (fun t -> exists (fun v -> not(is_var v))
                             (snd(strip_comb(rand(lhs(snd(strip_forall t)))))))
                      (conjuncts(snd(strip_exists
                         (snd(strip_forall(rand(concl irth6))))))) in
    let mk_newcon tm =
      let vs,bod = strip_forall tm in
      let rdeb = rand(lhs bod) in
      let rdef = list_mk_abs(vs,rdeb) in
      let newname = fst(dest_var(genvar bool_ty)) in
      let def = mk_eq(mk_var(newname,type_of rdef),rdef) in
      let dth = new_definition def in
      SIMPLE_BETA_RULE dth in
    let dths = map mk_newcon ncjs in
    let ith6,rth6 = CONJ_PAIR(PURE_REWRITE_RULE dths irth6) in
    n,ith6,rth6 in
  fun def ->
    let newtys = map fst def in
    let truecons = itlist (@) (map (map fst o snd) def) [] in
    let (p,ith0,rth0) = define_type_nested def in
    let avs,etm = strip_forall(concl rth0) in
    let allcls = conjuncts(snd(strip_exists etm)) in
    let relcls = fst(chop_list (length truecons) allcls) in
    let gencons =
      map (repeat rator o rand o lhand o snd o strip_forall) relcls in
    let cdefs =
      map2 (fun s r -> SYM(new_definition (mk_eq(mk_var(s,type_of r),r))))
           truecons gencons in
    let tavs = make_args "f" [] (map type_of avs) in
    let ith1 = SUBS cdefs ith0
    and rth1 = GENL tavs (SUBS cdefs (SPECL tavs rth0)) in
    let retval = p,ith1,rth1 in
    let newentries = map (fun s -> dest_vartype s,retval) newtys in
    (inductive_type_store := newentries @ (!inductive_type_store);
     do_list extend_rectype_net newentries; ith1,rth1);;

(* ----------------------------------------------------------------------- *)
(* The overall function, with rather crude string-based benignity.         *)
(* ----------------------------------------------------------------------- *)

let the_inductive_types = ref
 ["list = NIL | CONS A list",(list_INDUCT,list_RECURSION);
  "option = NONE | SOME A",(option_INDUCT,option_RECURSION);
  "sum = INL A | INR B",(sum_INDUCT,sum_RECURSION)];;

let define_type s =
  try let retval = assoc s (!the_inductive_types) in
      (warn true "Benign redefinition of inductive type"; retval)
  with Failure _ ->
      let defspec = parse_inductive_type_specification s in
      let newtypes = map fst defspec
      and constructors = itlist ((@) o map fst) (map snd defspec) [] in
      if not(length(setify newtypes) = length newtypes)
      then failwith "define_type: multiple definitions of a type"
      else if not(length(setify constructors) = length constructors)
      then failwith "define_type: multiple instances of a constructor"
      else if exists (can get_type_arity o dest_vartype) newtypes
      then let t = find (can get_type_arity) (map dest_vartype newtypes) in
           failwith("define_type: type :"^t^" already defined")
      else if exists (can get_const_type) constructors
      then let t = find (can get_const_type) constructors in
           failwith("define_type: constant "^t^" already defined")
      else
        let retval = define_type_raw defspec in
        the_inductive_types := (s,retval)::(!the_inductive_types); retval;;

(* ------------------------------------------------------------------------- *)
(* Unwinding, and application of patterns. Add easy cases to default net.    *)
(* ------------------------------------------------------------------------- *)

let UNWIND_CONV,MATCH_CONV =
  let pth_0 = prove
   (`(if ?!x. x = a /\ p then @x. x = a /\ p else @x. F) =
     (if p then a else @x. F)`,
    BOOL_CASES_TAC `p:bool` THEN ASM_REWRITE_TAC[COND_ID] THEN
    MESON_TAC[])
  and pth_1 = prove
   (`_MATCH x (_SEQPATTERN r s) =
     (if ?y. r x y then _MATCH x r else _MATCH x s) /\
    _FUNCTION (_SEQPATTERN r s) x =
     (if ?y. r x y then _FUNCTION r x else _FUNCTION s x)`,
    REWRITE_TAC[_MATCH; _SEQPATTERN; _FUNCTION] THEN
    MESON_TAC[])
  and pth_2 = prove
   (`((?y. _UNGUARDED_PATTERN (GEQ s t) (GEQ u y)) <=> s = t) /\
     ((?y. _GUARDED_PATTERN (GEQ s t) p (GEQ u y)) <=> s = t /\ p)`,
    REWRITE_TAC[_UNGUARDED_PATTERN; _GUARDED_PATTERN; GEQ_DEF] THEN
    MESON_TAC[])
  and pth_3 = prove
   (`(_MATCH x (\y z. P y z) = if ?!z. P x z then @z. P x z else @x. F) /\
     (_FUNCTION (\y z. P y z) x = if ?!z. P x z then @z. P x z else @x. F)`,
    REWRITE_TAC[_MATCH; _FUNCTION])
  and pth_4 = prove
   (`(_UNGUARDED_PATTERN (GEQ s t) (GEQ u y) <=> y = u /\ s = t) /\
     (_GUARDED_PATTERN (GEQ s t) p (GEQ u y) <=> y = u /\ s = t /\ p)`,
    REWRITE_TAC[_UNGUARDED_PATTERN; _GUARDED_PATTERN; GEQ_DEF] THEN
    MESON_TAC[])
  and pth_5 = prove
   (`(if ?!z. z = k then @z. z = k else @x. F) = k`,
    MESON_TAC[]) in
  let rec INSIDE_EXISTS_CONV conv tm =
    if is_exists tm then BINDER_CONV (INSIDE_EXISTS_CONV conv) tm
    else conv tm in
  let PUSH_EXISTS_CONV =
    let econv = REWR_CONV SWAP_EXISTS_THM in
    let rec conv bc tm =
      try (econv THENC BINDER_CONV(conv bc)) tm
      with Failure _ -> bc tm in
    conv in
  let BREAK_CONS_CONV =
    let conv2 = GEN_REWRITE_CONV DEPTH_CONV [AND_CLAUSES; OR_CLAUSES] THENC
                ASSOC_CONV CONJ_ASSOC in
    fun tm ->
      let conv0 = TOP_SWEEP_CONV(REWRITES_CONV(!basic_rectype_net)) in
      let conv1 = if is_conj tm then LAND_CONV conv0 else conv0 in
      (conv1 THENC conv2) tm in
  let UNWIND_CONV =
    let baseconv = GEN_REWRITE_CONV I
      [UNWIND_THM1; UNWIND_THM2;
       EQT_INTRO(SPEC_ALL EXISTS_REFL);
       EQT_INTRO(GSYM(SPEC_ALL EXISTS_REFL))] in
    let rec UNWIND_CONV tm =
      let evs,bod = strip_exists tm in
      let eqs = conjuncts bod in
      try let eq = find
           (fun tm -> is_eq tm &&
                      let l,r = dest_eq tm in
                      (mem l evs && not (free_in l r)) ||
                      (mem r evs && not (free_in r l))) eqs in
          let l,r = dest_eq eq in
          let v = if mem l evs && not (free_in l r) then l else r in
          let cjs' = eq::(subtract eqs [eq]) in
          let n = length evs - (1 + index v (rev evs)) in
          let th1 = CONJ_ACI_RULE(mk_eq(bod,list_mk_conj cjs')) in
          let th2 = itlist MK_EXISTS evs th1 in
          let th3 = funpow n BINDER_CONV (PUSH_EXISTS_CONV baseconv)
                      (rand(concl th2)) in
          CONV_RULE (RAND_CONV UNWIND_CONV) (TRANS th2 th3)
       with Failure _ -> REFL tm in
     UNWIND_CONV in
  let MATCH_SEQPATTERN_CONV =
    GEN_REWRITE_CONV I [pth_1] THENC
    RATOR_CONV(LAND_CONV
     (BINDER_CONV(RATOR_CONV BETA_CONV THENC BETA_CONV) THENC
      PUSH_EXISTS_CONV(GEN_REWRITE_CONV I [pth_2] THENC BREAK_CONS_CONV) THENC
      UNWIND_CONV THENC
      GEN_REWRITE_CONV DEPTH_CONV
       [EQT_INTRO(SPEC_ALL EQ_REFL); AND_CLAUSES] THENC
      GEN_REWRITE_CONV DEPTH_CONV [EXISTS_SIMP]))
  and MATCH_ONEPATTERN_CONV tm =
    let th1 = GEN_REWRITE_CONV I [pth_3] tm in
    let tm' = body(rand(lhand(rand(concl th1)))) in
    let th2 = (INSIDE_EXISTS_CONV
                (GEN_REWRITE_CONV I [pth_4] THENC
                 RAND_CONV BREAK_CONS_CONV) THENC
               UNWIND_CONV THENC
               GEN_REWRITE_CONV DEPTH_CONV
                [EQT_INTRO(SPEC_ALL EQ_REFL); AND_CLAUSES] THENC
               GEN_REWRITE_CONV DEPTH_CONV [EXISTS_SIMP])
              tm' in
    let conv tm = if tm = lhand(concl th2) then th2 else fail() in
    CONV_RULE
        (RAND_CONV (RATOR_CONV
          (COMB2_CONV (RAND_CONV (BINDER_CONV conv)) (BINDER_CONV conv))))
        th1 in
  let MATCH_SEQPATTERN_CONV_TRIV =
    MATCH_SEQPATTERN_CONV THENC
    GEN_REWRITE_CONV I [COND_CLAUSES]
  and MATCH_SEQPATTERN_CONV_GEN =
    MATCH_SEQPATTERN_CONV THENC
    GEN_REWRITE_CONV TRY_CONV [COND_CLAUSES]
  and MATCH_ONEPATTERN_CONV_TRIV =
    MATCH_ONEPATTERN_CONV THENC
    GEN_REWRITE_CONV I [pth_5]
  and MATCH_ONEPATTERN_CONV_GEN =
    MATCH_ONEPATTERN_CONV THENC
    GEN_REWRITE_CONV TRY_CONV [pth_0; pth_5] in
  do_list extend_basic_convs
   ["MATCH_SEQPATTERN_CONV",
    (`_MATCH x (_SEQPATTERN r s)`,MATCH_SEQPATTERN_CONV_TRIV);
    "FUN_SEQPATTERN_CONV",
    (`_FUNCTION (_SEQPATTERN r s) x`,MATCH_SEQPATTERN_CONV_TRIV);
    "MATCH_ONEPATTERN_CONV",
    (`_MATCH x (\y z. P y z)`,MATCH_ONEPATTERN_CONV_TRIV);
    "FUN_ONEPATTERN_CONV",
    (`_FUNCTION (\y z. P y z) x`,MATCH_ONEPATTERN_CONV_TRIV)];
  (CHANGED_CONV UNWIND_CONV,
   (MATCH_SEQPATTERN_CONV_GEN ORELSEC MATCH_ONEPATTERN_CONV_GEN));;

let FORALL_UNWIND_CONV =
  let PUSH_FORALL_CONV =
     let econv = REWR_CONV SWAP_FORALL_THM in
     let rec conv bc tm =
       try (econv THENC BINDER_CONV(conv bc)) tm
       with Failure _ -> bc tm in
     conv in
  let baseconv = GEN_REWRITE_CONV I
   [MESON[] `(!x. x = a /\ p x ==> q x) <=> (p a ==> q a)`;
    MESON[] `(!x. a = x /\ p x ==> q x) <=> (p a ==> q a)`;
    MESON[] `(!x. x = a ==> q x) <=> q a`;
    MESON[] `(!x. a = x ==> q x) <=> q a`] in
  let rec FORALL_UNWIND_CONV tm =
    try let avs,bod = strip_forall tm in
        let ant,con = dest_imp bod in
        let eqs = conjuncts ant in
        let eq = find (fun tm ->
          is_eq tm &&
          let l,r = dest_eq tm in
          (mem l avs && not (free_in l r)) ||
          (mem r avs && not (free_in r l))) eqs in
        let l,r = dest_eq eq in
        let v = if mem l avs && not (free_in l r) then l else r in
        let cjs' = eq::(subtract eqs [eq]) in
        let n = length avs - (1 + index v (rev avs)) in
        let th1 = CONJ_ACI_RULE(mk_eq(ant,list_mk_conj cjs')) in
        let th2 = AP_THM (AP_TERM (rator(rator bod)) th1) con in
        let th3 = itlist MK_FORALL avs th2 in
        let th4 = funpow n BINDER_CONV (PUSH_FORALL_CONV baseconv)
                    (rand(concl th3)) in
        CONV_RULE (RAND_CONV FORALL_UNWIND_CONV) (TRANS th3 th4)
    with Failure _ -> REFL tm in
  FORALL_UNWIND_CONV;;
