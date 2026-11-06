(* ========================================================================= *)
(* More sophisticated derived rules including definitions and rewriting.     *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                (c) Copyright, Michael Faerber 2018                        *)
(* ========================================================================= *)

needs "bool.ml";;

(* ------------------------------------------------------------------------- *)
(* Type of instantiations, with terms, types and higher-order data.          *)
(* ------------------------------------------------------------------------- *)

type instantiation =
  (int * term) list * (term * term) list * (hol_type * hol_type) list;;

(* ------------------------------------------------------------------------- *)
(* The last recourse when all else fails!                                    *)
(* ------------------------------------------------------------------------- *)

let mk_thm(asl,c) =
  let ax = new_axiom(itlist (curry mk_imp) (rev asl) c) in
  rev_itlist (fun t th -> MP th (ASSUME t)) (rev asl) ax;;

(* ------------------------------------------------------------------------- *)
(* Derived congruence rules; very useful things!                             *)
(* ------------------------------------------------------------------------- *)

let MK_CONJ =
  let andtm = `(/\)` in
  fun eq1 eq2 -> MK_COMB(AP_TERM andtm eq1,eq2);;

let MK_DISJ =
  let ortm = `(\/)` in
  fun eq1 eq2 -> MK_COMB(AP_TERM ortm eq1,eq2);;

let MK_FORALL =
  let atm = mk_const("!",[]) in
  fun v th -> AP_TERM (inst [type_of v,aty] atm) (ABS v th);;

let MK_EXISTS =
  let atm = mk_const("?",[]) in
  fun v th -> AP_TERM (inst [type_of v,aty] atm) (ABS v th);;

(* ------------------------------------------------------------------------- *)
(* Eliminate the antecedent of a theorem using a conversion/proof rule.      *)
(* ------------------------------------------------------------------------- *)

let MP_CONV (cnv:conv) th =
  let l,r = dest_imp(concl th) in
  let ath = cnv l in
  try MP th (EQT_ELIM ath) with Failure _ -> MP th ath;;

(* ------------------------------------------------------------------------- *)
(* Multiple beta-reduction (we use a slight variant below).                  *)
(* ------------------------------------------------------------------------- *)

let rec BETAS_CONV tm =
  match tm with
    Comb(Abs(_,_),_) -> BETA_CONV tm
  | Comb(Comb(_,_),_) -> (RATOR_CONV BETAS_CONV THENC BETA_CONV) tm
  | _ -> failwith "BETAS_CONV";;

(* ------------------------------------------------------------------------- *)
(* Instantiators.                                                            *)
(* ------------------------------------------------------------------------- *)

let (instantiate :instantiation->term->term) =
  let betas n tm =
    let args,lam = funpow n (fun (l,t) -> (rand t)::l,rator t) ([],tm) in
    rev_itlist (fun a l -> let v,b = dest_abs l in vsubst[a,v] b) args lam in
  let rec ho_betas bcs pat tm =
    if is_var pat || is_const pat then fail() else
    try let bv,bod = dest_abs tm in
        mk_abs(bv,ho_betas bcs (body pat) bod)
    with Failure _ ->
        let hop,args = strip_comb pat in
        try let n = rev_assoc hop bcs in
            if length args = n then betas n tm else fail()
        with Failure _ ->
            let lpat,rpat = dest_comb pat in
            let ltm,rtm = dest_comb tm in
            try let lth = ho_betas bcs lpat ltm in
                try let rth = ho_betas bcs rpat rtm in
                    mk_comb(lth,rth)
                with Failure _ ->
                    mk_comb(lth,rtm)
            with Failure _ ->
                let rth = ho_betas bcs rpat rtm in
                mk_comb(ltm,rth) in
  fun (bcs,tmin,tyin) tm ->
    let itm = if tyin = [] then tm else inst tyin tm in
    if tmin = [] then itm else
    let ttm = vsubst tmin itm in
    if bcs = [] then ttm else
    try ho_betas bcs itm ttm with Failure _ -> ttm;;

let (INSTANTIATE : instantiation->thm->thm) =
  let rec BETAS_CONV n tm =
    if n = 1 then TRY_CONV BETA_CONV tm else
    (RATOR_CONV (BETAS_CONV (n-1)) THENC
     TRY_CONV BETA_CONV) tm in
  let rec HO_BETAS bcs pat tm =
    if is_var pat || is_const pat then fail() else
    try let bv,bod = dest_abs tm in
        ABS bv (HO_BETAS bcs (body pat) bod)
    with Failure _ ->
        let hop,args = strip_comb pat in
        try let n = rev_assoc hop bcs in
            if length args = n then BETAS_CONV n tm else fail()
        with Failure _ ->
            let lpat,rpat = dest_comb pat in
            let ltm,rtm = dest_comb tm in
            try let lth = HO_BETAS bcs lpat ltm in
                try let rth = HO_BETAS bcs rpat rtm in
                    MK_COMB(lth,rth)
                with Failure _ ->
                    AP_THM lth rtm
            with Failure _ ->
                let rth = HO_BETAS bcs rpat rtm in
                AP_TERM ltm rth in
  fun (bcs,tmin,tyin) th ->
    let ith = if tyin = [] then th else INST_TYPE tyin th in
    if tmin = [] then ith else
    let tth = INST tmin ith in
    if hyp tth = hyp th then
      if bcs = [] then tth else
      try let eth = HO_BETAS bcs (concl ith) (concl tth) in
          EQ_MP eth tth
      with Failure _ -> tth
    else failwith "INSTANTIATE: term or type var free in assumptions";;

let (INSTANTIATE_ALL : instantiation->thm->thm) =
  fun ((_,tmin,tyin) as i) th ->
    if tmin = [] && tyin = [] then th else
    let hyps = hyp th in
    if hyps = [] then INSTANTIATE i th else
    let tyrel,tyiirel =
      if tyin = [] then [],hyps else
      let tvs = itlist (union o tyvars o snd) tyin [] in
      partition (fun tm -> let tvs' = type_vars_in_term tm in
                           not(intersect tvs tvs' = [])) hyps in
    let tmrel,tmirrel =
      if tmin = [] then [],tyiirel else
      let vs = itlist (union o frees o snd) tmin [] in
      partition (fun tm -> let vs' = frees tm in
                           not (intersect vs vs' = [])) tyiirel in
    let rhyps = union tyrel tmrel in
    let th1 = rev_itlist DISCH rhyps th in
    let th2 = INSTANTIATE i th1 in
    funpow (length rhyps) UNDISCH th2;;

(* ------------------------------------------------------------------------- *)
(* Higher order matching of terms.                                           *)
(*                                                                           *)
(* Note: in the event of spillover patterns, this may return false results;  *)
(* but there's usually an implicit check outside that the match worked       *)
(* anyway. A test could be put in (see if any "env" variables are left in    *)
(* the term after abstracting out the pattern instances) but it'd be slower. *)
(* ------------------------------------------------------------------------- *)

let (term_match:term list -> term -> term -> instantiation) =
  let safe_inserta ((y,x) as n) l =
    try let z = rev_assoc x l in
        if aconv y z then l else failwith "safe_inserta"
    with Failure "find" -> n::l in

  let safe_insert ((y,x) as n) l =
    try let z = rev_assoc x l in
        if compare y z = 0 then l else failwith "safe_insert"
    with Failure "find" -> n::l in

  let mk_dummy =
    let name = fst(dest_var(genvar aty)) in
    fun ty -> mk_var(name,ty) in

  let rec term_pmatch lconsts env vtm ctm ((insts,homs) as sofar) =
    match (vtm,ctm) with
      Var(_,_),_ ->
       (try let ctm' = rev_assoc vtm env in
            if compare ctm' ctm = 0 then sofar
            else failwith "term_pmatch"
        with Failure "find" ->
            if mem vtm lconsts then
              if compare ctm vtm = 0 then sofar
              else failwith "term_pmatch: can't instantiate local constant"
            else safe_inserta (ctm,vtm) insts,homs)
    | Const(vname,vty),Const(cname,cty) ->
        if compare vname cname = 0 then
          if compare vty cty = 0 then sofar
          else safe_insert (mk_dummy cty,mk_dummy vty) insts,homs
        else failwith "term_pmatch"
    | Abs(vv,vbod),Abs(cv,cbod) ->
        let sofar' = safe_insert
          (mk_dummy(snd(dest_var cv)),mk_dummy(snd(dest_var vv))) insts,homs in
        term_pmatch lconsts ((cv,vv)::env) vbod cbod sofar'
    | _ ->
      let vhop = repeat rator vtm in
      if is_var vhop && not (mem vhop lconsts) &&
                       not (can (rev_assoc vhop) env) then
        let vty = type_of vtm and cty = type_of ctm in
        let insts' =
          if compare vty cty = 0 then insts
          else safe_insert (mk_dummy cty,mk_dummy vty) insts in
        (insts',(env,ctm,vtm)::homs)
      else
        let lv,rv = dest_comb vtm
        and lc,rc = dest_comb ctm in
        let sofar' = term_pmatch lconsts env lv lc sofar in
        term_pmatch lconsts env rv rc sofar' in

  let get_type_insts insts =
    itlist (fun (t,x) -> type_match (snd(dest_var x)) (type_of t)) insts in

  let separate_insts insts =
      let realinsts,patterns = partition (is_var o snd) insts in
      let betacounts =
        if patterns = [] then [] else
        itlist
          (fun (_,p) sof ->
            let hop,args = strip_comb p in
            try safe_insert (length args,hop) sof with Failure _ ->
            (warn true "Inconsistent patterning in higher order match"; sof))
          patterns [] in
      let tyins = get_type_insts realinsts [] in
      betacounts,
      mapfilter (fun (t,x) ->
        let x' = let xn,xty = dest_var x in
                 mk_var(xn,type_subst tyins xty) in
        if compare t x' = 0 then fail() else (t,x')) realinsts,
      tyins in

  let rec term_homatch lconsts tyins (insts,homs) =
    if homs = [] then insts else
    let (env,ctm,vtm) = hd homs in
    if is_var vtm then
      if compare ctm vtm = 0
       then term_homatch lconsts tyins (insts,tl homs) else
      let newtyins = safe_insert (type_of ctm,snd(dest_var vtm)) tyins
      and newinsts = (ctm,vtm)::insts in
      term_homatch lconsts newtyins (newinsts,tl homs) else
    let vhop,vargs = strip_comb vtm in
    let afvs = freesl vargs in
    let inst_fn = inst tyins in
    try let tmins = map
          (fun a -> (try rev_assoc a env with Failure _ -> try
                         rev_assoc a insts with Failure _ ->
                         if mem a lconsts then a else fail()),
                    inst_fn a) afvs in
        let pats0 = map inst_fn vargs in
        let pats = map (vsubst tmins) pats0 in
        let vhop' = inst_fn vhop in
        let ni =
          let chop,cargs = strip_comb ctm in
          if compare cargs pats = 0 then
            if compare chop vhop = 0
            then insts else safe_inserta (chop,vhop) insts else
          let ginsts = map
            (fun p -> (if is_var p then p else genvar(type_of p)),p) pats in
          let ctm' = subst ginsts ctm
          and gvs = map fst ginsts in
          let abstm = list_mk_abs(gvs,ctm') in
          let vinsts = safe_inserta (abstm,vhop) insts in
          let icpair = ctm',list_mk_comb(vhop',gvs) in
          icpair::vinsts in
        term_homatch lconsts tyins (ni,tl homs)
    with Failure _ ->
        let lc,rc = dest_comb ctm
        and lv,rv = dest_comb vtm in
        let pinsts_homs' =
          term_pmatch lconsts env rv rc (insts,(env,lc,lv)::(tl homs)) in
        let tyins' = get_type_insts (fst pinsts_homs') [] in
        term_homatch lconsts tyins' pinsts_homs' in

  fun lconsts vtm ctm ->
    let pinsts_homs = term_pmatch lconsts [] vtm ctm ([],[]) in
    let tyins = get_type_insts (fst pinsts_homs) [] in
    let insts = term_homatch lconsts tyins pinsts_homs in
    separate_insts insts;;

(* ------------------------------------------------------------------------- *)
(* First order unification of terms of the same type.                        *)
(* ------------------------------------------------------------------------- *)

let (term_unify:term list -> term -> term -> instantiation) =
  let augment1 sofar (s,x) =
    let s' = subst sofar s in
    if vfree_in x s' && not (s = x) then failwith "term_unify: augment1"
    else (s',x) in
  let raw_augment_insts p insts =
    p::(map (augment1 [p]) insts) in
  let augment_insts(t,v) insts =
    let t' = vsubst insts t in
    if t' = v then insts
    else if vfree_in v t' then failwith "augment_insts"
    else raw_augment_insts (t',v) insts in
  let rec unify vars tm1 tm2 sofar =
    if tm1 = tm2 then sofar
    else if is_var tm1 && mem tm1 vars then
      try let tm1' = rev_assoc tm1 sofar in
          unify vars tm1' tm2 sofar
      with Failure "find" ->
          augment_insts (tm2,tm1) sofar
    else if is_var tm2 && mem tm2 vars then
       try let tm2' = rev_assoc tm2 sofar in
          unify vars tm1 tm2' sofar
      with Failure "find" ->
          augment_insts (tm1,tm2) sofar
    else if is_abs tm1 then
      let tm1' = body tm1
      and tm2' = subst [bndvar tm1,bndvar tm2] (body tm2) in
      unify vars tm1' tm2' sofar
    else
      let l1,r1 = dest_comb tm1
      and l2,r2 = dest_comb tm2 in
      unify vars l1 l2 (unify vars r1 r2 sofar) in
  fun vars tm1 tm2 -> [],unify vars tm1 tm2 [],[];;

(* ------------------------------------------------------------------------- *)
(* Unification of types.                                                     *)
(* ------------------------------------------------------------------------- *)

let type_unify : hol_type -> hol_type -> (hol_type * hol_type) list
                 -> (hol_type * hol_type) list =
  let augment1 sofar (s,x) =
    let s' = type_subst sofar s in
    if occurs_in x s' && not (s = x) then failwith "type_unify: augment1"
    else (s',x) in
  let raw_augment_insts p insts =
    p::(map (augment1 [p]) insts) in
  let augment_insts(ty,v) insts =
    let ty' = type_subst insts ty in
    if ty' = v then insts
    else if occurs_in v ty' then failwith "type_unify: augment_insts"
    else raw_augment_insts (ty',v) insts in
  let rec unify ty1 ty2 sofar =
    if ty1 = ty2 then sofar
    else if is_vartype ty1 then
      try let ty1' = rev_assoc ty1 sofar in
          unify ty1' ty2 sofar
      with Failure "find" ->
          augment_insts (ty2,ty1) sofar
    else if is_vartype ty2 then
       try let ty2' = rev_assoc ty2 sofar in
          unify ty1 ty2' sofar
      with Failure "find" ->
          augment_insts (ty1,ty2) sofar
    else
      let l1,r1 = dest_type ty1
      and l2,r2 = dest_type ty2 in
      if l1 = l2 then itlist2 unify r1 r2 sofar
      else failwith "unify_type" in
  unify;;

(* ------------------------------------------------------------------------- *)
(* Unification of terms and their types together.                            *)
(* ------------------------------------------------------------------------- *)

let term_type_unify : term -> term -> instantiation -> instantiation =
  let augment_tyinsts (s, t) tyinsts =
    let sty = type_of (inst tyinsts s)
    and tty = type_of (inst tyinsts t) in
    let tyinsts' = type_unify sty tty [] in
    tyinsts' @ map (fun (ty, v) -> type_subst tyinsts' ty, v) tyinsts in
  let augment1 sofar (s,x) =
    let s' = subst sofar s in
    if vfree_in x s' && not (s = x) then failwith "term_unify: augment1"
    else (s',x) in
  let raw_augment_insts p (tminsts, tyinsts) =
    p::(map (augment1 [p]) tminsts), tyinsts in
  let augment_insts(t,v) (tminsts, tyinsts) =
    let tminsts' = map (fun (t, v) -> inst tyinsts t, inst tyinsts v) tminsts in
    let t' = inst tyinsts (vsubst tminsts' t) in
    let v' = inst tyinsts v in
    let sofar' = (tminsts', tyinsts) in
    if t' = v' then sofar'
    else if vfree_in v' t' then failwith "term_unify: augment_insts"
    else raw_augment_insts (t',v') sofar' in
  let rec unify tm1 tm2 (tminsts, tyinsts as sofar) =
    if tm1 = tm2 then sofar
    else if is_var tm1 then
      try let tm1' = rev_assoc tm1 tminsts in
          unify tm1' tm2 sofar
      with Failure "find" ->
          augment_insts (tm2,tm1) (tminsts, augment_tyinsts (tm1, tm2) tyinsts)
    else if is_var tm2 then
       try let tm2' = rev_assoc tm2 tminsts in
          unify tm1 tm2' sofar
      with Failure "find" ->
          augment_insts (tm1,tm2) (tminsts, augment_tyinsts (tm1, tm2) tyinsts)
    else if is_abs tm1 then
      let tm1' = body tm1
      and tm2' = subst [bndvar tm1,bndvar tm2] (body tm2) in
      unify tm1' tm2' sofar
    else if is_const tm1 then
      if name_of tm1 <> name_of tm2 then failwith "term_unify"
      else tminsts, augment_tyinsts (tm1, tm2) tyinsts
    else
      let l1,r1 = dest_comb tm1
      and l2,r2 = dest_comb tm2 in
      unify l1 l2 (unify r1 r2 sofar) in
  fun tm1 tm2 (it, tminsts, tyinsts) ->
    let tminsts', tyinsts' = unify tm1 tm2 (tminsts, tyinsts) in
    it,tminsts',tyinsts';;

(* ------------------------------------------------------------------------- *)
(* Modify bound variable names at depth. (Not very efficient...)             *)
(* ------------------------------------------------------------------------- *)

let deep_alpha =
  let tryalpha v tm =
    try alpha v tm
    with Failure _ -> try
        let v' = variant (frees tm) v in
        alpha v' tm
    with Failure _ -> tm in
  let rec deep_alpha env tm =
    if env = [] then tm else
    try let v,bod = dest_abs tm in
        let vn,vty = dest_var v in
        try let (vn',_),newenv = remove (fun (_,x) -> x = vn) env in
            let v' = mk_var(vn',vty) in
            let tm' = tryalpha v' tm in
            let iv,ib = dest_abs tm' in
            mk_abs(iv,deep_alpha newenv ib)
        with Failure _ -> mk_abs(v,deep_alpha env bod)
    with Failure _ -> try
        let l,r = dest_comb tm in
        mk_comb(deep_alpha env l,deep_alpha env r)
    with Failure _ -> tm in
  deep_alpha;;

(* ------------------------------------------------------------------------- *)
(* Instantiate theorem by matching part of it to a term.                     *)
(* The GEN_PART_MATCH version renames free vars to avoid clashes.            *)
(* ------------------------------------------------------------------------- *)

let PART_MATCH,GEN_PART_MATCH =
  let rec match_bvs t1 t2 acc =
    try let v1,b1 = dest_abs t1
        and v2,b2 = dest_abs t2 in
        let n1 = fst(dest_var v1) and n2 = fst(dest_var v2) in
        let newacc = if n1 = n2 then acc else insert (n1,n2) acc in
        match_bvs b1 b2 newacc
    with Failure _ -> try
        let l1,r1 = dest_comb t1
        and l2,r2 = dest_comb t2 in
        match_bvs l1 l2 (match_bvs r1 r2 acc)
    with Failure _ -> acc in
  let PART_MATCH partfn th =
    let sth = SPEC_ALL th in
    let bod = concl sth in
    let pbod = partfn bod in
    let lconsts = intersect (frees (concl th)) (freesl(hyp th)) in
    fun tm ->
      let bvms = match_bvs tm pbod [] in
      let abod = deep_alpha bvms bod in
      let ath = EQ_MP (ALPHA bod abod) sth in
      let insts = term_match lconsts (partfn abod) tm in
      let fth = INSTANTIATE insts ath in
      if hyp fth <> hyp ath then failwith "PART_MATCH: instantiated hyps" else
      let tm' = partfn (concl fth) in
      if compare tm' tm = 0 then fth else
      try SUBS[ALPHA tm' tm] fth
      with Failure _ -> failwith "PART_MATCH: Sanity check failure"
  and GEN_PART_MATCH partfn th =
    let sth = SPEC_ALL th in
    let bod = concl sth in
    let pbod = partfn bod in
    let lconsts = intersect (frees (concl th)) (freesl(hyp th)) in
    let fvs = subtract (subtract (frees bod) (frees pbod)) lconsts in
    fun tm ->
      let bvms = match_bvs tm pbod [] in
      let abod = deep_alpha bvms bod in
      let ath = EQ_MP (ALPHA bod abod) sth in
      let insts = term_match lconsts (partfn abod) tm in
      let eth = INSTANTIATE insts (GENL fvs ath) in
      let fth = itlist (fun v th -> snd(SPEC_VAR th)) fvs eth in
      if hyp fth <> hyp ath then failwith "PART_MATCH: instantiated hyps" else
      let tm' = partfn (concl fth) in
      if compare tm' tm = 0 then fth else
      try SUBS[ALPHA tm' tm] fth
      with Failure _ -> failwith "PART_MATCH: Sanity check failure" in
  PART_MATCH,GEN_PART_MATCH;;

(* ------------------------------------------------------------------------- *)
(* Matching modus ponens.                                                    *)
(* ------------------------------------------------------------------------- *)

let MATCH_MP ith =
  let sth =
    try let tm = concl ith in
        let avs,bod = strip_forall tm in
        let ant,con = dest_imp bod in
        let svs,pvs = partition (C vfree_in ant) avs in
        if pvs = [] then ith else
        let th1 = SPECL avs (ASSUME tm) in
        let th2 = GENL svs (DISCH ant (GENL pvs (UNDISCH th1))) in
        MP (DISCH tm th2) ith
    with Failure _ -> failwith "MATCH_MP: Not an implication" in
  let match_fun = PART_MATCH (fst o dest_imp) sth in
  fun th -> try MP (match_fun (concl th)) th
            with Failure _ -> failwith "MATCH_MP: No match";;

(* ------------------------------------------------------------------------- *)
(* Useful instance of more general higher order matching.                    *)
(* ------------------------------------------------------------------------- *)

let HIGHER_REWRITE_CONV =
  let BETA_VAR =
    let rec BETA_CONVS n =
      if n = 1 then TRY_CONV BETA_CONV else
      RATOR_CONV (BETA_CONVS (n - 1)) THENC TRY_CONV BETA_CONV in
    let rec free_beta v tm =
      if is_abs tm then
        let bv,bod = dest_abs tm in
        if v = bv then failwith "unchanged" else
        ABS_CONV(free_beta v bod) else
      let op,args = strip_comb tm in
      if args = [] then failwith "unchanged" else
      if op = v then BETA_CONVS (length args) else
      let l,r = dest_comb tm in
      try let lconv = free_beta v l in
          (try let rconv = free_beta v r in
               COMB2_CONV lconv rconv
           with Failure _ -> RATOR_CONV lconv)
      with Failure _ -> RAND_CONV (free_beta v r) in
    free_beta in
  let GINST th =
    let fvs = subtract (frees(concl th)) (freesl (hyp th)) in
    let gvs = map (genvar o type_of) fvs in
    INST (zip gvs fvs) th in
  fun ths ->
    let thl = map (GINST o SPEC_ALL) ths in
    let concs = map concl thl in
    let lefts = map lhs concs in
    let preds,pats = unzip(map dest_comb lefts) in
    let beta_fns = map2 BETA_VAR preds concs in
    let ass_list = zip pats (zip preds (zip thl beta_fns)) in
    let mnet = itlist (fun p n -> enter [] (p,p) n) pats empty_net in
    let look_fn t =
      mapfilter (fun p -> if can (term_match [] p) t then p else fail())
                (lookup t mnet) in
    fun top tm ->
      let pred t = not (look_fn t = []) && free_in t tm in
      let stm = if top then find_term pred tm
                else hd(sort free_in (find_terms pred tm)) in
      let pat = hd(look_fn stm) in
      let _,tmin,tyin = term_match [] pat stm in
      let pred,(th,beta_fn) = assoc pat ass_list in
      let gv = genvar(type_of stm) in
      let abs = mk_abs(gv,subst[gv,stm] tm) in
      let _,tmin0,tyin0 = term_match [] pred abs in
      CONV_RULE beta_fn (INST tmin (INST tmin0 (INST_TYPE tyin0 th)));;

(* ------------------------------------------------------------------------- *)
(* Derived principle of definition justifying |- c x1 .. xn = t[x1,..,xn]    *)
(* ------------------------------------------------------------------------- *)

let new_definition tm =
  let avs,bod = strip_forall tm in
  let l,r = try dest_eq bod
    with Failure _ -> failwith "new_definition: Not an equation" in
  let lv,largs = strip_comb l in
  let rtm = try list_mk_abs(largs,r)
    with Failure _ -> failwith "new_definition: Non-variable in LHS pattern" in
  let def = mk_eq(lv,rtm) in
  let th1 = new_basic_definition def in
  let th2 = rev_itlist
    (fun tm th -> let ith = AP_THM th tm in
                  TRANS ith (BETA_CONV(rand(concl ith)))) largs th1 in
  let rvs = filter (not o C mem avs) largs in
  itlist GEN rvs (itlist GEN avs th2);;
