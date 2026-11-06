(* ========================================================================= *)
(* System of tactics (slightly different from any traditional LCF method).   *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                 (c) Copyright, Marco Maggesi 2012                         *)
(* ========================================================================= *)

needs "drule.ml";;

(* ------------------------------------------------------------------------- *)
(* The common case of trivial instantiations.                                *)
(* ------------------------------------------------------------------------- *)

let null_inst = ([],[],[] :instantiation);;

let null_meta = (([]:term list),null_inst);;

(* ------------------------------------------------------------------------- *)
(* A goal has labelled assumptions, and the hyps are now thms.               *)
(* ------------------------------------------------------------------------- *)

type goal = (string * thm) list * term;;

let equals_goal ((a,w):goal) ((a',w'):goal) =
  forall2 (fun (s,th) (s',th') -> s = s' && equals_thm th th') a a' && w = w';;

(* ------------------------------------------------------------------------- *)
(* A justification function for a goalstate [A1 ?- g1; ...; An ?- gn],       *)
(* starting from an initial goal A ?- g, is a function f such that for any   *)
(* instantiation @:                                                          *)
(*                                                                           *)
(*   f(@) [A1@ |- g1@; ...; An@ |- gn@] = A@ |- g@                           *)
(* ------------------------------------------------------------------------- *)

type justification = instantiation -> thm list -> thm;;

(* ------------------------------------------------------------------------- *)
(* The goalstate stores the subgoals, justification, current instantiation,  *)
(* and a list of metavariables.                                              *)
(* ------------------------------------------------------------------------- *)

type goalstate = (term list * instantiation) * goal list * justification;;

(* ------------------------------------------------------------------------- *)
(* A goalstack is just a list of goalstates. Could go for more...            *)
(* ------------------------------------------------------------------------- *)

type goalstack = goalstate list;;

(* ------------------------------------------------------------------------- *)
(* A refinement, applied to a goalstate [A1 ?- g1; ...; An ?- gn]            *)
(* yields a new goalstate with updated justification function, to            *)
(* give a possibly-more-instantiated version of the initial goal.            *)
(* ------------------------------------------------------------------------- *)

type refinement = goalstate -> goalstate;;

(* ------------------------------------------------------------------------- *)
(* A tactic, applied to a goal A ?- g, returns:                              *)
(*                                                                           *)
(*  o A list of new metavariables introduced                                 *)
(*  o An instantiation (%)                                                   *)
(*  o A list of subgoals                                                     *)
(*  o A justification f such that for any instantiation @ we have            *)
(*    f(@) [A1@  |- g1@; ...; An@ |- gn@] = A(%;@) |- g(%;@)                 *)
(* ------------------------------------------------------------------------- *)

type tactic = goal -> goalstate;;

type thm_tactic = thm -> tactic;;

type thm_tactical = thm_tactic -> thm_tactic;;

(* ------------------------------------------------------------------------- *)
(* Apply instantiation to a goal.                                            *)
(* ------------------------------------------------------------------------- *)

let (inst_goal:instantiation->goal->goal) =
  fun p (thms,w) ->
    map (I F_F INSTANTIATE_ALL p) thms,instantiate p w;;

(* ------------------------------------------------------------------------- *)
(* Perform a sequential composition (left first) of instantiations.          *)
(* ------------------------------------------------------------------------- *)

let (compose_insts :instantiation->instantiation->instantiation) =
  fun (pats1,tmin1,tyin1) ((pats2,tmin2,tyin2) as i2) ->
    let tmin = map (instantiate i2 F_F inst tyin2) tmin1
    and tyin = map (type_subst tyin2 F_F I) tyin1 in
    let tmin' = filter (fun (_,x) -> not (can (rev_assoc x) tmin)) tmin2
    and tyin' = filter (fun (_,a) -> not (can (rev_assoc a) tyin)) tyin2 in
    pats1@pats2,tmin@tmin',tyin@tyin';;

(* ------------------------------------------------------------------------- *)
(* Construct A,_FALSITY_ |- p; contortion so falsity is the last element.    *)
(* ------------------------------------------------------------------------- *)

let _FALSITY_ = new_definition `_FALSITY_ = F`;;

let mk_fthm =
  let pth = UNDISCH(fst(EQ_IMP_RULE _FALSITY_))
  and qth = ASSUME `_FALSITY_` in
  fun (asl,c) -> PROVE_HYP qth (itlist ADD_ASSUM (rev asl) (CONTR c pth));;

(* ------------------------------------------------------------------------- *)
(* Validity checking of tactics. This cannot be 100% accurate without making *)
(* arbitrary theorems, but "mk_fthm" brings us quite close.                  *)
(* ------------------------------------------------------------------------- *)

let (VALID:tactic->tactic) =
  let fake_thm (asl,w) =
    let asms = itlist (union o hyp o snd) asl [] in
    mk_fthm(asms,w)
  and false_tm = `_FALSITY_` in
  fun tac (asl,w) ->
    let ((mvs,i),gls,just as res) = tac (asl,w) in
    let ths = map fake_thm gls in
    let asl',w' = dest_thm(just null_inst ths) in
    let asl'',w'' = inst_goal i (asl,w) in
    let maxasms =
      itlist (fun (_,th) -> union (insert (concl th) (hyp th))) asl'' [] in
    if aconv w' w'' &&
       forall (fun t -> exists (aconv t) maxasms) (subtract asl' [false_tm])
    then res else failwith "VALID: Invalid tactic";;

(* ------------------------------------------------------------------------- *)
(* Various simple combinators for tactics, identity tactic etc.              *)
(* ------------------------------------------------------------------------- *)

let (THEN),(THENL),then1_ =
  let propagate_empty i [] = []
  and propagate_thm th i [] = INSTANTIATE_ALL i th in
  let compose_justs n just1 just2 insts2 i ths =
    let ths1,ths2 = chop_list n ths in
    (just1 (compose_insts insts2 i) ths1)::(just2 i ths2) in
  let rec seqapply l1 l2 = match (l1,l2) with
     ([],[]) -> null_meta,[],propagate_empty
   | ((tac:tactic)::tacs),((goal:goal)::goals) ->
            let ((mvs1,insts1),gls1,just1) = tac goal in
            let goals' = map (inst_goal insts1) goals in
            let ((mvs2,insts2),gls2,just2) = seqapply tacs goals' in
            ((union mvs1 mvs2,compose_insts insts1 insts2),
             (map (inst_goal insts2) gls1)@gls2,compose_justs (length gls1) just1 just2 insts2)
   | _,_ -> failwith "seqapply: Length mismatch" in
  let justsequence just1 just2 insts2 i ths =
    just1 (compose_insts insts2 i) (just2 i ths) in
  let tacsequence ((mvs1,insts1),gls1,just1) tacl =
    let ((mvs2,insts2),gls2,just2) = seqapply tacl gls1 in
    let jst = justsequence just1 just2 insts2 in
    let just = if gls2 = [] then propagate_thm (jst null_inst []) else jst in
    ((union mvs1 mvs2,compose_insts insts1 insts2),gls2,just) in
  let (then_: tactic -> tactic -> tactic) =
    fun tac1 tac2 g ->
      let _,gls,_ as gstate = tac1 g in
      tacsequence gstate (replicate tac2 (length gls))
  and (thenl_: tactic -> tactic list -> tactic) =
    fun tac1 tac2l g ->
      let _,gls,_ as gstate = tac1 g in
      if gls = [] then tacsequence gstate []
      else tacsequence gstate tac2l in
  then_,thenl_,(fun tac1 tac2 -> thenl_ tac1 [tac2]);;

let ((ORELSE): tactic -> tactic -> tactic) =
  fun tac1 tac2 g ->
    try tac1 g with Failure _ -> tac2 g;;

let (FAIL_TAC: string -> tactic) =
  fun tok g -> failwith tok;;

let (NO_TAC: tactic) =
  FAIL_TAC "NO_TAC";;

let (ALL_TAC:tactic) =
  fun g -> null_meta,[g],fun _ [th] -> th;;

let TRY tac =
  tac ORELSE ALL_TAC;;

let rec REPEAT tac g =
  ((tac THEN REPEAT tac) ORELSE ALL_TAC) g;;

let EVERY tacl =
  itlist (fun t1 t2 -> t1 THEN t2) tacl ALL_TAC;;

let (FIRST: tactic list -> tactic) =
  fun tacl g -> end_itlist (fun t1 t2 -> t1 ORELSE t2) tacl g;;

let MAP_EVERY tacf lst =
  EVERY (map tacf lst);;

let MAP_FIRST tacf lst =
  FIRST (map tacf lst);;

let (CHANGED_TAC: tactic -> tactic) =
  fun tac g ->
    let (meta,gl,_ as gstate) = tac g in
    if meta = null_meta && length gl = 1 && equals_goal (hd gl) g
    then failwith "CHANGED_TAC" else gstate;;

let rec REPLICATE_TAC n tac =
  if n <= 0 then ALL_TAC else tac THEN (REPLICATE_TAC (n - 1) tac);;

(* ------------------------------------------------------------------------- *)
(* Combinators for theorem continuations / "theorem tacticals".              *)
(* ------------------------------------------------------------------------- *)

let ((THEN_TCL): thm_tactical -> thm_tactical -> thm_tactical) =
  fun ttcl1 ttcl2 ttac -> ttcl1 (ttcl2 ttac);;

let ((ORELSE_TCL): thm_tactical -> thm_tactical -> thm_tactical) =
  fun ttcl1 ttcl2 ttac th ->
    try ttcl1 ttac th with Failure _ -> ttcl2 ttac th;;

let rec REPEAT_TCL ttcl ttac th =
  ((ttcl THEN_TCL (REPEAT_TCL ttcl)) ORELSE_TCL I) ttac th;;

let (REPEAT_GTCL: thm_tactical -> thm_tactical) =
  let rec REPEAT_GTCL ttcl ttac th g =
    try ttcl (REPEAT_GTCL ttcl ttac) th g with Failure _ -> ttac th g in
  REPEAT_GTCL;;

let (ALL_THEN: thm_tactical) =
  I;;

let (NO_THEN: thm_tactical) =
  fun ttac th -> failwith "NO_THEN";;

let EVERY_TCL ttcll =
  itlist (fun t1 t2 -> t1 THEN_TCL t2) ttcll ALL_THEN;;

let FIRST_TCL ttcll =
  end_itlist (fun t1 t2 -> t1 ORELSE_TCL t2) ttcll;;

(* ------------------------------------------------------------------------- *)
(* Tactics to augment assumption list. Note that to allow "ASSUME p" for     *)
(* any assumption "p", these add a PROVE_HYP in the justification function,  *)
(* just in case.                                                             *)
(* ------------------------------------------------------------------------- *)

let (LABEL_TAC: string -> thm_tactic) =
  fun s thm (asl,w) ->
    null_meta,[(s,thm)::asl,w],
    fun i [th] -> PROVE_HYP (INSTANTIATE_ALL i thm) th;;

let ASSUME_TAC = LABEL_TAC "";;

(* ------------------------------------------------------------------------- *)
(* Manipulation of assumption list.                                          *)
(* ------------------------------------------------------------------------- *)

let (FIND_ASSUM: thm_tactic -> term -> tactic) =
  fun ttac t ((asl,w) as g) ->
    ttac(snd(find (fun (_,th) -> concl th = t) asl)) g;;

let (POP_ASSUM: thm_tactic -> tactic) =
  fun ttac ->
   function (((_,th)::asl),w) -> ttac th (asl,w)
    | _ -> failwith "POP_ASSUM: No assumption to pop";;

let (ASSUM_LIST: (thm list -> tactic) -> tactic) =
    fun aslfun (asl,w) -> aslfun (map snd asl) (asl,w);;

let (POP_ASSUM_LIST: (thm list -> tactic) -> tactic) =
  fun asltac (asl,w) -> asltac (map snd asl) ([],w);;

let (EVERY_ASSUM: thm_tactic -> tactic) =
  fun ttac -> ASSUM_LIST (MAP_EVERY ttac);;

let (FIRST_ASSUM: thm_tactic -> tactic) =
  fun ttac (asl,w as g) -> tryfind (fun (_,th) -> ttac th g) asl;;

let (RULE_ASSUM_TAC :(thm->thm)->tactic) =
  fun rule (asl,w) -> (POP_ASSUM_LIST(K ALL_TAC) THEN
                       MAP_EVERY (fun (s,th) -> LABEL_TAC s (rule th))
                                 (rev asl)) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Operate on assumption identified by a label.                              *)
(* ------------------------------------------------------------------------- *)

let (USE_THEN:string->thm_tactic->tactic) =
  fun s ttac (asl,w as gl) ->
    let th = try assoc s asl with Failure _ ->
             failwith("USE_TAC: didn't find assumption "^s) in
    ttac th gl;;

let (REMOVE_THEN:string->thm_tactic->tactic) =
  fun s ttac (asl,w) ->
    let th = try assoc s asl with Failure _ ->
             failwith("USE_TAC: didn't find assumption "^s) in
    let asl1,asl2 = chop_list(index s (map fst asl)) asl in
    let asl' = asl1 @ tl asl2 in
    ttac th (asl',w);;

let NAME_ASSUMS_TAC: tactic =
  fun (asl,g) ->
    let idx: int ref = ref 0 in
    let has (name:string) = exists (fun (name',_) -> name = name') asl in
    let rec next_hyp_name (): string =
      let n = "H" ^ (string_of_int !idx) in
      idx := !idx + 1;
      if has n then next_hyp_name ()
      else n in
    let asl = map
      (fun (name,a) -> if name = "" then (next_hyp_name(),a) else (name,a))
      asl in
    ALL_TAC (asl,g);;

(* ------------------------------------------------------------------------- *)
(* General tools to augment a required set of theorems with assumptions.     *)
(* Here ASM uses all current hypotheses of the goal, while HYP uses only     *)
(* those whose labels are given in the string argument.                      *)
(* ------------------------------------------------------------------------- *)

let (ASM :(thm list -> tactic)->(thm list -> tactic)) =
  fun tltac ths (asl,w as g) -> tltac (map snd asl @ ths) g;;

let HYP =
  let ident = function
      Ident s::rest when isalnum s -> s,rest
    | _ -> raise Noparse in
  let parse_using = many ident in
  let HYP_LIST tac l =
    rev_itlist (fun s k l -> USE_THEN s (fun th -> k (th::l))) l tac in
  fun tac s ->
    let l,rest = (fix "Using pattern" parse_using o lex o explode) s in
    if rest=[] then HYP_LIST tac l else failwith "Invalid using pattern";;

(* ------------------------------------------------------------------------- *)
(* Basic tactic to use a theorem equal to the goal. Does *no* matching.      *)
(* ------------------------------------------------------------------------- *)

let (ACCEPT_TAC: thm_tactic) =
  let propagate_thm th i [] = INSTANTIATE_ALL i th in
  fun th (asl,w) ->
    if aconv (concl th) w then
      null_meta,[],propagate_thm th
    else failwith "ACCEPT_TAC";;

(* ------------------------------------------------------------------------- *)
(* Create tactic from a conversion. This allows the conversion to return     *)
(* |- p rather than |- p = T on a term "p". It also eliminates any goals of  *)
(* the form "T" automatically.                                               *)
(* ------------------------------------------------------------------------- *)

let (CONV_TAC: conv -> tactic) =
  let t_tm = `T` in
  fun conv ((asl,w) as g) ->
    let th = conv w in
    let tm = concl th in
    if aconv tm w then ACCEPT_TAC th g else
    let l,r = dest_eq tm in
    if not(aconv l w) then failwith "CONV_TAC: bad equation" else
    if r = t_tm then ACCEPT_TAC(EQT_ELIM th) g else
    let th' = SYM th in
    null_meta,[asl,r],fun i [th] -> EQ_MP (INSTANTIATE_ALL i th') th;;

(* ------------------------------------------------------------------------- *)
(* Tactics for equality reasoning.                                           *)
(* ------------------------------------------------------------------------- *)

let (REFL_TAC: tactic) =
  fun ((asl,w) as g) ->
    try ACCEPT_TAC(REFL(rand w)) g
    with Failure _ -> failwith "REFL_TAC";;

let (ABS_TAC: tactic) =
  fun (asl,w) ->
    try let l,r = dest_eq w in
        let lv,lb = dest_abs l
        and rv,rb = dest_abs r in
        let avoids = itlist (union o thm_frees o snd) asl (frees w) in
        let v = mk_primed_var avoids lv in
        null_meta,[asl,mk_eq(vsubst[v,lv] lb,vsubst[v,rv] rb)],
        fun i [th] -> let ath = ABS v th in
                      EQ_MP (ALPHA (concl ath) (instantiate i w)) ath
    with Failure _ -> failwith "ABS_TAC";;

let (MK_COMB_TAC: tactic) =
  fun (asl,gl) ->
    try let l,r = dest_eq gl in
        let f,x = dest_comb l
        and g,y = dest_comb r in
        null_meta,[asl,mk_eq(f,g); asl,mk_eq(x,y)],
        fun _ [th1;th2] -> MK_COMB(th1,th2)
    with Failure _ -> failwith "MK_COMB_TAC";;

let (AP_TERM_TAC: tactic) =
  let tac = MK_COMB_TAC THENL [REFL_TAC; ALL_TAC] in
  fun gl -> try tac gl with Failure _ -> failwith "AP_TERM_TAC";;

let (AP_THM_TAC: tactic) =
  let tac = MK_COMB_TAC THENL [ALL_TAC; REFL_TAC] in
  fun gl -> try tac gl with Failure _ -> failwith "AP_THM_TAC";;

let (BINOP_TAC: tactic) =
  let tac = MK_COMB_TAC THENL [AP_TERM_TAC; ALL_TAC] in
  fun gl -> try tac gl with Failure _ -> failwith "AP_THM_TAC";;

let (SUBST1_TAC: thm_tactic) =
  fun th -> CONV_TAC(SUBS_CONV [th]);;

let SUBST_ALL_TAC rth =
  SUBST1_TAC rth THEN RULE_ASSUM_TAC (SUBS [rth]);;

let BETA_TAC = CONV_TAC(REDEPTH_CONV BETA_CONV);;

(* ------------------------------------------------------------------------- *)
(* Just use an equation to substitute if possible and uninstantiable.        *)
(* ------------------------------------------------------------------------- *)

let SUBST_VAR_TAC th =
  try let asm,eq = dest_thm th in
      let l,r = dest_eq eq in
      if aconv l r then ALL_TAC
      else if not (subset (frees eq) (freesl asm)) then fail()
      else if (is_const l || is_var l) && not(free_in l r)
           then SUBST_ALL_TAC th
      else if (is_const r || is_var r) && not(free_in r l)
           then SUBST_ALL_TAC(SYM th)
      else fail()
  with Failure _ -> failwith "SUBST_VAR_TAC";;

(* ------------------------------------------------------------------------- *)
(* Basic logical tactics.                                                    *)
(* ------------------------------------------------------------------------- *)

let (DISCH_TAC: tactic) =
  let f_tm = `F` in
  fun (asl,w) ->
    try let ant,c = dest_imp w in
        let th1 = ASSUME ant in
        null_meta,[("",th1)::asl,c],
        fun i [th] -> DISCH (instantiate i ant) th
    with Failure _ -> try
        let ant = dest_neg w in
        let th1 = ASSUME ant in
        null_meta,[("",th1)::asl,f_tm],
        fun i [th] -> NOT_INTRO(DISCH (instantiate i ant) th)
    with Failure _ -> failwith "DISCH_TAC";;

let (MP_TAC: thm_tactic) =
  fun thm (asl,w) ->
    null_meta,[asl,mk_imp(concl thm,w)],
    fun i [th] -> MP th (INSTANTIATE_ALL i thm);;

let (EQ_TAC: tactic) =
  fun (asl,w) ->
    try let l,r = dest_eq w in
        null_meta,[asl, mk_imp(l,r); asl, mk_imp(r,l)],
        fun _ [th1; th2] -> IMP_ANTISYM_RULE th1 th2
    with Failure _ -> failwith "EQ_TAC";;

let (UNDISCH_TAC: term -> tactic) =
 fun tm (asl,w) ->
   try let sthm,asl' = remove (fun (_,asm) -> aconv (concl asm) tm) asl in
       let thm = snd sthm in
       null_meta,[asl',mk_imp(tm,w)],
       fun i [th] -> MP th (INSTANTIATE_ALL i thm)
   with Failure _ -> failwith "UNDISCH_TAC";;

let (SPEC_TAC: term * term -> tactic) =
  fun (t,x) (asl,w) ->
    try null_meta,[asl, mk_forall(x,subst[x,t] w)],
        fun i [th] -> SPEC (instantiate i t) th
    with Failure _ -> failwith "SPEC_TAC";;

let (X_GEN_TAC: term -> tactic),
    (X_CHOOSE_TAC: term -> thm_tactic),
    (EXISTS_TAC: term -> tactic) =
  let tactic_type_compatibility_check pfx e g =
    let et = type_of e and gt = type_of g in
    if et = gt then ()
    else failwith(pfx ^ ": expected type :"^string_of_type et^" but got :"^
                  string_of_type gt) in
  let X_GEN_TAC x' =
    if not(is_var x') then failwith "X_GEN_TAC: not a variable" else
    fun (asl,w) ->
        let x,bod = try dest_forall w
          with Failure _ -> failwith "X_GEN_TAC: Not universally quantified" in
        let _ = tactic_type_compatibility_check "X_GEN_TAC" x x' in
        let avoids = itlist (union o thm_frees o snd) asl (frees w) in
        if mem x' avoids then failwith "X_GEN_TAC: invalid variable" else
        let afn = CONV_RULE(GEN_ALPHA_CONV x) in
        null_meta,[asl,vsubst[x',x] bod],
        fun i [th] -> afn (GEN x' th)
  and X_CHOOSE_TAC x' xth =
        let xtm = concl xth in
        let x,bod = try dest_exists xtm
         with Failure _ -> failwith "X_CHOOSE_TAC: not existential" in
        let _ = tactic_type_compatibility_check "X_CHOOSE_TAC" x x' in
        let pat = vsubst[x',x] bod in
        let xth' = ASSUME pat in
        fun (asl,w) ->
          let avoids = itlist (union o frees o concl o snd) asl
                              (union (frees w) (thm_frees xth)) in
          if mem x' avoids then failwith "X_CHOOSE_TAC: invalid variable" else
          null_meta,[("",xth')::asl,w],
          fun i [th] -> CHOOSE(x',INSTANTIATE_ALL i xth) th
  and EXISTS_TAC t (asl,w) =
    let v,bod = try dest_exists w with Failure _ ->
                failwith "EXISTS_TAC: Goal not existentially quantified" in
    let _ = tactic_type_compatibility_check "EXISTS_TAC" v t in
    null_meta,[asl,vsubst[t,v] bod],
    fun i [th] -> EXISTS (instantiate i w,instantiate i t) th in
  X_GEN_TAC,X_CHOOSE_TAC,EXISTS_TAC;;

let (GEN_TAC: tactic) =
  fun (asl,w) ->
    try let x = fst(dest_forall w) in
        let avoids = itlist (union o thm_frees o snd) asl (frees w) in
        let x' = mk_primed_var avoids x in
        X_GEN_TAC x' (asl,w)
    with Failure _ -> failwith "GEN_TAC";;

let (CHOOSE_TAC: thm_tactic) =
  fun xth ->
    try let x = fst(dest_exists(concl xth)) in
        fun (asl,w) ->
          let avoids = itlist (union o thm_frees o snd) asl
                              (union (frees w) (thm_frees xth)) in
          let x' = mk_primed_var avoids x in
          X_CHOOSE_TAC x' xth (asl,w)
      with Failure _ -> failwith "CHOOSE_TAC";;

let (CONJ_TAC: tactic) =
  fun (asl,w) ->
    try let l,r = dest_conj w in
        null_meta,[asl,l; asl,r],fun _ [th1;th2] -> CONJ th1 th2
    with Failure _ -> failwith "CONJ_TAC";;

let (DISJ1_TAC: tactic) =
  fun (asl,w) ->
    try let l,r = dest_disj w in
        null_meta,[asl,l],fun i [th] -> DISJ1 th (instantiate i r)
    with Failure _ -> failwith "DISJ1_TAC";;

let (DISJ2_TAC: tactic) =
  fun (asl,w) ->
    try let l,r = dest_disj w in
          null_meta,[asl,r],fun i [th] -> DISJ2 (instantiate i l) th
    with Failure _ -> failwith "DISJ2_TAC";;

let (DISJ_CASES_TAC: thm_tactic) =
  fun dth ->
    try let dtm = concl dth in
        let l,r = dest_disj dtm in
        let thl = ASSUME l
        and thr = ASSUME r in
        fun (asl,w) ->
          null_meta,[("",thl)::asl,w; ("",thr)::asl,w],
          fun i [th1;th2] -> DISJ_CASES (INSTANTIATE_ALL i dth) th1 th2
    with Failure _ -> failwith "DISJ_CASES_TAC";;

let (CONTR_TAC: thm_tactic) =
  let propagate_thm th i [] = INSTANTIATE_ALL i th in
  fun cth (asl,w) ->
    try let th = CONTR w cth in
        null_meta,[],propagate_thm th
    with Failure _ -> failwith "CONTR_TAC";;

let (MATCH_ACCEPT_TAC:thm_tactic) =
  let propagate_thm th i [] = INSTANTIATE_ALL i th in
  let rawtac th (asl,w) =
    try let ith = PART_MATCH I th w in
        null_meta,[],propagate_thm ith
    with Failure _ -> failwith "ACCEPT_TAC" in
  fun th -> REPEAT GEN_TAC THEN rawtac th;;

let (MATCH_MP_TAC :thm_tactic) =
  fun th ->
    let sth =
      try let tm = concl th in
          let avs,bod = strip_forall tm in
          let ant,con = dest_imp bod in
          let th1 = SPECL avs (ASSUME tm) in
          let th2 = UNDISCH th1 in
          let evs = filter (fun v -> vfree_in v ant && not (vfree_in v con))
                           avs in
          let th3 = itlist SIMPLE_CHOOSE evs (DISCH tm th2) in
          let tm3 = hd(hyp th3) in
          MP (DISCH tm (GEN_ALL (DISCH tm3 (UNDISCH th3)))) th
      with Failure _ -> failwith "MATCH_MP_TAC: Bad theorem" in
    let match_fun = PART_MATCH (snd o dest_imp) sth in
    fun (asl,w) -> try let xth = match_fun w in
                       let lant = fst(dest_imp(concl xth)) in
                       null_meta,[asl,lant],
                       fun i [th] -> MP (INSTANTIATE_ALL i xth) th
                   with Failure _ -> failwith "MATCH_MP_TAC: No match";;

let (TRANS_TAC:thm->term->tactic) =
  fun th ->
    let ctm = snd(strip_forall(concl th)) in
    let cl,cr = dest_conj(lhand ctm) in
    let x = lhand cl and y = rand cl and z = rand cr in
    fun tm (asl,w as gl) ->
      let lop,r = dest_comb w in
      let op,l = dest_comb lop in
      let ilist =
        itlist2 type_match (map type_of [x;y;z])(map type_of [l;tm;r]) [] in
      let th' = INST_TYPE ilist th in
      (MATCH_MP_TAC th' THEN EXISTS_TAC tm) gl;;

(* ------------------------------------------------------------------------- *)
(* Theorem continuations.                                                    *)
(* ------------------------------------------------------------------------- *)

let (CONJUNCTS_THEN2:thm_tactic->thm_tactic->thm_tactic) =
  fun ttac1 ttac2 cth ->
      let c1,c2 = dest_conj(concl cth) in
      fun gl -> let ti,gls,jfn = (ttac1(ASSUME c1) THEN ttac2(ASSUME c2)) gl in
                let jfn' i ths =
                  let th1,th2 = CONJ_PAIR(INSTANTIATE_ALL i cth) in
                  PROVE_HYP th1 (PROVE_HYP th2 (jfn i ths)) in
                ti,gls,jfn';;

let (CONJUNCTS_THEN: thm_tactical) =
  W CONJUNCTS_THEN2;;

let (DISJ_CASES_THEN2:thm_tactic->thm_tactic->thm_tactic) =
  fun ttac1 ttac2 cth ->
    DISJ_CASES_TAC cth THENL [POP_ASSUM ttac1; POP_ASSUM ttac2];;

let (DISJ_CASES_THEN: thm_tactical) =
  W DISJ_CASES_THEN2;;

let (DISCH_THEN: thm_tactic -> tactic) =
  fun ttac -> DISCH_TAC THEN POP_ASSUM ttac;;

let (X_CHOOSE_THEN: term -> thm_tactical) =
  fun x ttac th -> X_CHOOSE_TAC x th THEN POP_ASSUM ttac;;

let (CHOOSE_THEN: thm_tactical) =
  fun ttac th -> CHOOSE_TAC th THEN POP_ASSUM ttac;;

(* ------------------------------------------------------------------------- *)
(* Various derived tactics and theorem continuations.                        *)
(* ------------------------------------------------------------------------- *)

let STRIP_THM_THEN =
  FIRST_TCL [CONJUNCTS_THEN; DISJ_CASES_THEN; CHOOSE_THEN];;

let (ANTE_RES_THEN: thm_tactical) =
  fun ttac ante ->
    ASSUM_LIST
     (fun asl ->
        let tacs = mapfilter (fun imp -> ttac (MATCH_MP imp ante)) asl in
        if tacs = [] then failwith "IMP_RES_THEN"
        else EVERY tacs);;

let (IMP_RES_THEN: thm_tactical) =
  fun ttac imp ->
    ASSUM_LIST
     (fun asl ->
        let tacs = mapfilter (fun ante -> ttac (MATCH_MP imp ante)) asl in
        if tacs = [] then failwith "IMP_RES_THEN"
        else EVERY tacs);;

let STRIP_ASSUME_TAC =
  let DISCARD_TAC th =
    let tm = concl th in
    fun (asl,w as g) ->
       if exists (fun a -> aconv tm (concl(snd a))) asl then ALL_TAC g
       else failwith "DISCARD_TAC: not already present" in
  (REPEAT_TCL STRIP_THM_THEN)
  (fun gth -> FIRST [CONTR_TAC gth; ACCEPT_TAC gth;
                     DISCARD_TAC gth; ASSUME_TAC gth]);;

let STRUCT_CASES_THEN ttac = REPEAT_TCL STRIP_THM_THEN ttac;;

let STRUCT_CASES_TAC = STRUCT_CASES_THEN
     (fun th -> SUBST1_TAC th ORELSE ASSUME_TAC th);;

let STRIP_GOAL_THEN ttac =  FIRST [GEN_TAC; CONJ_TAC; DISCH_THEN ttac];;

let (STRIP_TAC: tactic) =
  fun g ->
    try STRIP_GOAL_THEN STRIP_ASSUME_TAC g
    with Failure _ -> failwith "STRIP_TAC";;

let (UNDISCH_THEN:term->thm_tactic->tactic) =
  fun tm ttac (asl,w) ->
    let thp,asl' = remove (fun (_,th) -> aconv (concl th) tm) asl in
    ttac (snd thp) (asl',w);;

let FIRST_X_ASSUM ttac =
    FIRST_ASSUM(fun th -> UNDISCH_THEN (concl th) ttac);;

(* ------------------------------------------------------------------------- *)
(* Subgoaling and freezing variables (latter is especially useful now).      *)
(* ------------------------------------------------------------------------- *)

let (SUBGOAL_THEN: term -> thm_tactic -> tactic) =
  fun wa ttac (asl,w) ->
    let meta,gl,just = ttac (ASSUME wa) (asl,w) in
    meta,(asl,wa)::gl,fun i l -> PROVE_HYP (hd l) (just i (tl l));;

let SUBGOAL_TAC s tm prfs =
  match prfs with
   p::ps -> (warn (ps <> []) "SUBGOAL_TAC: additional subproofs ignored";
             SUBGOAL_THEN tm (LABEL_TAC s) THENL [p; ALL_TAC])
  | [] -> failwith "SUBGOAL_TAC: no subproof given";;

let (FREEZE_THEN :thm_tactical) =
  fun ttac th (asl,w) ->
    let meta,gl,just = ttac (ASSUME(concl th)) (asl,w) in
    meta,gl,fun i l -> PROVE_HYP th (just i l);;

(* ------------------------------------------------------------------------- *)
(* Metavariable tactics.                                                     *)
(* ------------------------------------------------------------------------- *)

let (X_META_EXISTS_TAC: term -> tactic) =
  fun t (asl,w) ->
    try if not (is_var t) then fail() else
        let v,bod = dest_exists w in
        ([t],null_inst),[asl,vsubst[t,v] bod],
        fun i [th] -> EXISTS (instantiate i w,instantiate i t) th
    with Failure _ -> failwith "X_META_EXISTS_TAC";;

let META_EXISTS_TAC ((asl,w) as gl) =
  let v = fst(dest_exists w) in
  let avoids = itlist (union o frees o concl o snd) asl (frees w) in
  let v' = mk_primed_var avoids v in
  X_META_EXISTS_TAC v' gl;;

let (META_SPEC_TAC: term -> thm -> tactic) =
  fun t thm (asl,w) ->
    let sth = SPEC t thm in
    ([t],null_inst),[(("",sth)::asl),w],
    fun i [th] -> PROVE_HYP (SPEC (instantiate i t) thm) th;;

(* ------------------------------------------------------------------------- *)
(* If all else fails!                                                        *)
(* ------------------------------------------------------------------------- *)

let (CHEAT_TAC:tactic) =
  fun (asl,w) -> ACCEPT_TAC(mk_thm([],w)) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Intended for time-consuming rules; delays evaluation till it sees goal.   *)
(* ------------------------------------------------------------------------- *)

let RECALL_ACCEPT_TAC r a g = ACCEPT_TAC(time r a) g;;

(* ------------------------------------------------------------------------- *)
(* Split off antecedent of antecedent as a subgoal.                          *)
(* ------------------------------------------------------------------------- *)

let ANTS_TAC =
  let tm1 = `p /\ (q ==> r)`
  and tm2 = `p ==> q` in
  let th1,th2 = CONJ_PAIR(ASSUME tm1) in
  let th = itlist DISCH [tm1;tm2] (MP th2 (MP(ASSUME tm2) th1)) in
  MATCH_MP_TAC th THEN CONJ_TAC;;

(* ------------------------------------------------------------------------- *)
(* A printer for goals etc.                                                  *)
(* ------------------------------------------------------------------------- *)

(* A parameter to prettyprinter's max boxes for printing hypotheses.         *)
(* Set to None if the formatter's default max boxes value is to be used.     *)
let print_goal_hyp_max_boxes = ref None;;

let (pp_print_goal:Format.formatter->goal->unit),
    (pp_print_colored_goal:Format.formatter->goal->unit) =
  let with_color (color_flag:bool) =
    let string_of_int3 n =
      if n < 10 then "  "^string_of_int n
      else if n < 100 then " "^string_of_int n
      else string_of_int n in
    let print_hyp fmt n (s,th) =
      pp_open_hbox fmt ();
      Format.pp_print_string fmt (string_of_int3 n);
      Format.pp_print_string fmt " [";
      pp_open_hvbox fmt 0;
      let old_max_boxes = pp_get_max_boxes fmt () in
      (match !print_goal_hyp_max_boxes with
      | None -> ()
      | Some hb -> pp_set_max_boxes fmt hb);
      (if color_flag then pp_print_colored_qterm else pp_print_qterm)
        fmt (concl th);
      pp_set_max_boxes fmt old_max_boxes;
      pp_close_box fmt ();
      Format.pp_print_string fmt "]";
      (if not (s = "") then (Format.pp_print_string fmt (" ("^s^")")) else ());
      pp_close_box fmt ();
      Format.pp_print_newline fmt () in
    let rec print_hyps fmt n asl =
      if asl = [] then () else
      (print_hyp fmt n (hd asl);
      print_hyps fmt (n + 1) (tl asl)) in
    fun fmt (asl,w) ->
      Format.pp_print_newline fmt ();
      if asl <> []
      then (print_hyps fmt 0 (rev asl); Format.pp_print_newline fmt ())
      else ();
      (if color_flag then pp_print_colored_qterm else pp_print_qterm) fmt w;
      Format.pp_print_newline fmt () in
  with_color false, with_color true;;

let (pp_print_goalstack:Format.formatter->goalstack->unit),
    (pp_print_colored_goalstack:Format.formatter->goalstack->unit) =
  let print_goalstate color_flag fmt k gs =
    let (_,gl,_) = gs in
    let n = length gl in
    let s = if n = 0 then "No subgoals" else
              (string_of_int k)^" subgoal"^(if k > 1 then "s" else "")
           ^" ("^(string_of_int n)^" total)" in
    Format.pp_print_string fmt s; Format.pp_print_newline fmt ();
    if gl = [] then () else
    do_list
      ((if color_flag then pp_print_colored_goal else pp_print_goal) fmt
        o C el gl)
      (rev(0--(k-1))) in
  let fn color_flag fmt l =
    if l = [] then Format.pp_print_string fmt "Empty goalstack"
    else if tl l = [] then
      let (_,gl,_ as gs) = hd l in
      print_goalstate color_flag fmt 1 gs
    else
      let (_,gl,_ as gs) = hd l
      and (_,gl0,_) = hd(tl l) in
      let p = length gl - length gl0 in
      let p' = if p < 1 then 1 else p + 1 in
      print_goalstate color_flag fmt p' gs in
  fn false, fn true;;

let print_goal = pp_print_goal Format.std_formatter;;
let print_goalstack = pp_print_goalstack Format.std_formatter;;
let PRINT_GOAL_TAC: tactic = fun gl -> print_goal gl; ALL_TAC gl;;
let PRINT_COLORED_GOAL_TAC: tactic =
    fun gl -> pp_print_colored_goal Format.std_formatter gl; ALL_TAC gl;;
let REMARK_TAC (s:string): tactic = fun gl -> remark s; ALL_TAC gl;;

(* ------------------------------------------------------------------------- *)
(* Convert a tactic into a refinement on head subgoal in current state.      *)
(* ------------------------------------------------------------------------- *)

let (by:tactic->refinement) =
  fun tac ((mvs,inst),gls,just) ->
    if gls = [] then failwith "No goal set" else
    let g = hd gls
    and ogls = tl gls in
    let ((newmvs,newinst),subgls,subjust) = tac g in
    let n = length subgls in
    let mvs' = union newmvs mvs
    and inst' = compose_insts inst newinst
    and gls' = subgls @ map (inst_goal newinst) ogls in
    let just' i ths =
      let i' = compose_insts inst' i in
      let cths,oths = chop_list n ths in
      let sths = (subjust i cths) :: oths in
      just i' sths in
    (mvs',inst'),gls',just';;

(* ------------------------------------------------------------------------- *)
(* Rotate the goalstate either way.                                          *)
(* ------------------------------------------------------------------------- *)

let (rotate:int->refinement) =
  let rotate_p (meta,sgs,just) =
    let sgs' = (tl sgs)@[hd sgs] in
    let just' i ths =
      let ths' = (last ths)::(butlast ths) in
      just i ths' in
    (meta,sgs',just')
  and rotate_n (meta,sgs,just) =
    let sgs' = (last sgs)::(butlast sgs) in
    let just' i ths =
      let ths' = (tl ths)@[hd ths] in
      just i ths' in
    (meta,sgs',just') in
  fun n -> if n > 0 then funpow n rotate_p
           else funpow (-n) rotate_n;;

(* ------------------------------------------------------------------------- *)
(* Perform refinement proof, tactic proof etc.                               *)
(* ------------------------------------------------------------------------- *)

let (mk_goalstate:goal->goalstate) =
  fun (asl,w) ->
    if type_of w = bool_ty then
      null_meta,[asl,w],
      (fun inst [th] -> INSTANTIATE_ALL inst th)
    else failwith "mk_goalstate: Non-boolean goal";;

let (TAC_PROOF : goal * tactic -> thm) =
  fun (g,tac) ->
    let gstate = mk_goalstate g in
    let _,sgs,just = by tac gstate in
    if sgs = [] then just null_inst []
    else failwith "TAC_PROOF: Unsolved goals";;

let prove(t,tac) =
  let th = TAC_PROOF(([],t),tac) in
  let asl,t' = dest_thm th in
  if asl <> [] then failwith "prove: additional assumptions in result"
  else if t' = t then th else
  try EQ_MP (ALPHA t' t) th
  with Failure _ -> failwith "prove: justification generated wrong theorem";;

(* ------------------------------------------------------------------------- *)
(* Interactive "subgoal package" stuff.                                      *)
(* ------------------------------------------------------------------------- *)

let current_goalstack = ref ([] :goalstack);;

let (refine:refinement->goalstack) =
  fun r ->
    let l = !current_goalstack in
    if l = [] then failwith "No current goal" else
    let h = hd l in
    let res = r h :: l in
    current_goalstack := res;
    !current_goalstack;;

let flush_goalstack() =
  let l = !current_goalstack in
  current_goalstack := [hd l];;

let e tac = refine(by(VALID tac));;

let r n = refine(rotate n);;

(* A sequence of 'e tac; r n' where n is the number of subgoals after e tac. *)
(* This command is useful when you want to interactively try a list of       *)
(* tactics after THENL, e.g.,                                                *)
(*   TAC THENL [ TAC_A; TAC_B; .. ]                                          *)
(* 'e TAC;; er TAC_A;;' will execute TAC, execute TAC_A, then switch to the  *)
(* second subgoal of 'e TAC' which will be the input goalstate of TAC_B.     *)
let er tac =
  let e_result = e tac in
  let n_subgoals_to_rotate, n_subgoals =
    match !current_goalstack with
    | (_,gl,_)::(_,glprev,_)::_ ->
      let n_subgoals = length gl in
      if n_subgoals = 0 then 0, 0
      else (n_subgoals - length glprev + 1), n_subgoals
    | _ -> failwith "current_goalstack must have at least 2 items after 'e'" in

  if n_subgoals_to_rotate = 0 || n_subgoals = 1 then begin
    remark "(Rotating zero subgoal)\n\n";
    e_result
  end else begin
    (if !verbose then print_goalstack !current_goalstack);
    remark (Printf.sprintf "\n(Rotating %d subgoal%s...)\n\n"
        n_subgoals_to_rotate
        (if n_subgoals_to_rotate = 1 then "" else "s"));
    let new_g = r n_subgoals_to_rotate in
    (* pop the latest subgoal so that one b() can fully roll back the state *)
    let cur_gs = !current_goalstack in
    let _ = current_goalstack := hd cur_gs :: tl (tl cur_gs) in
    new_g
  end;;

let set_goal(asl,w) =
  current_goalstack :=
    [mk_goalstate(map (fun t -> "",ASSUME t) asl,w)];
  !current_goalstack;;

let g t =
  let fvs = sort (<) (map (fst o dest_var) (frees t)) in
  (if fvs <> [] then
     let errmsg = end_itlist (fun s t -> s^", "^t) fvs in
     warn true ("Free variables in goal: "^errmsg)
   else ());
   set_goal([],t);;

let b() =
  let l = !current_goalstack in
  if length l = 1 then failwith "Can't back up any more" else
  current_goalstack := tl l;
  !current_goalstack;;

let p() =
  !current_goalstack;;

let top_realgoal() =
  let (_,((asl,w)::_),_)::_ = !current_goalstack in
  asl,w;;

let top_goal() =
  let asl,w = top_realgoal() in
  map (concl o snd) asl,w;;

let top_thm() =
  let (_,[],f)::_ = !current_goalstack in
  f null_inst [];;
