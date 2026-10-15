(* ========================================================================= *)
(* Definition by primitive recursion and other tools for inductive types.    *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "nums.ml";;

(* ------------------------------------------------------------------------- *)
(* Prove existence of recursive function. The inner "raw" version requires   *)
(* exact correspondence with recursion theorem; "canon" requires the         *)
(* PR argument to come first in the arg list; the outer one is more general. *)
(* ------------------------------------------------------------------------- *)

let prove_recursive_functions_exist =
  let prove_raw_recursive_functions_exist ax tm =
    let rawcls = conjuncts tm in
    let spcls = map (snd o strip_forall) rawcls in
    let lpats = map (strip_comb o lhand) spcls in
    let ufns = itlist (insert o fst) lpats [] in
    let axth = SPEC_ALL ax in
    let exvs,axbody = strip_exists (concl axth) in
    let axcls = conjuncts axbody in
    let f = fst o dest_const o repeat rator o rand o
            lhand o snd o strip_forall in
    let findax = C assoc (map (fun t -> f t,t) axcls) in
    let raxs =
      map (findax o fst o dest_const o repeat rator o hd o snd) lpats in
    let axfns = map (repeat rator o lhand o snd o strip_forall) raxs in
    let urfns = map (fun v -> assocd v (setify (zip axfns (map fst lpats))) v)
                    exvs in
    let axtm = list_mk_exists(exvs,list_mk_conj raxs)
    and urtm = list_mk_exists(urfns,tm) in
    let insts = term_match [] axtm urtm in
    let ixth = INSTANTIATE insts axth in
    let ixvs,ixbody = strip_exists (concl ixth) in
    let ixtm = subst (zip urfns ixvs) ixbody in
    let ixths = CONJUNCTS (ASSUME ixtm) in
    let rixths = map (fun t -> find (aconv t o concl) ixths) rawcls in
    let rixth = itlist SIMPLE_EXISTS ufns (end_itlist CONJ rixths) in
    PROVE_HYP ixth (itlist SIMPLE_CHOOSE urfns rixth) in
  let canonize t =
    let avs,bod = strip_forall t in
    let l,r = dest_eq bod in
    let fn,args = strip_comb l in
    let rarg = hd args
    and vargs = tl args in
    let l' = mk_comb(fn,rarg)
    and r' = list_mk_abs(vargs,r) in
    let fvs = frees rarg in
    let def = ASSUME(list_mk_forall(fvs,mk_eq(l',r'))) in
    GENL avs (RIGHT_BETAS vargs (SPECL fvs def)) in
  let prove_canon_recursive_functions_exist ax tm =
    let ths = map canonize (conjuncts tm) in
    let atm = list_mk_conj (map (hd o hyp) ths) in
    let aths = CONJUNCTS(ASSUME atm) in
    let rth = end_itlist CONJ (map2 PROVE_HYP aths ths) in
    let eth = prove_raw_recursive_functions_exist ax atm in
    let evs = fst(strip_exists(concl eth)) in
    PROVE_HYP eth (itlist SIMPLE_CHOOSE evs (itlist SIMPLE_EXISTS evs rth)) in
  let reshuffle fn args acc =
    let args' = uncurry (C (@)) (partition is_var args) in
    if args = args' then acc else
    let gvs = map (genvar o type_of) args in
    let gvs' = map (C assoc (zip args gvs)) args' in
    let lty = itlist (mk_fun_ty o type_of) gvs'
              (funpow (length gvs) (hd o tl o snd o dest_type) (type_of fn)) in
    let fn' = genvar lty in
    let def = mk_eq(fn,list_mk_abs(gvs,list_mk_comb(fn',gvs'))) in
    (ASSUME def)::acc
  and scrub_def t th =
    let l,r = dest_eq t in
    MP (INST [r,l] (DISCH t th)) (REFL r) in
  fun ax tm ->
    let rawcls = conjuncts tm in
    let spcls = map (snd o strip_forall) rawcls in
    let lpats = map (strip_comb o lhand) spcls in
    let ufns = itlist (insert o fst) lpats [] in
    let uxargs = map (C assoc lpats) ufns in
    let trths = itlist2 reshuffle ufns uxargs [] in
    let tth = GEN_REWRITE_CONV REDEPTH_CONV (BETA_THM::trths) tm in
    let eth = prove_canon_recursive_functions_exist ax (rand(concl tth)) in
    let evs,ebod = strip_exists(concl eth) in
    let fth = itlist SIMPLE_EXISTS ufns (EQ_MP (SYM tth) (ASSUME ebod)) in
    let gth = itlist scrub_def (map concl trths) fth in
    PROVE_HYP eth (itlist SIMPLE_CHOOSE evs gth);;

(* ------------------------------------------------------------------------- *)
(* Version that defines function(s).                                         *)
(* ------------------------------------------------------------------------- *)

let new_recursive_definition =
  let the_recursive_definitions = ref [] in
  let find_redefinition tm th =
    let th' = PART_MATCH I th tm in
    ignore(PART_MATCH I th' (concl th)); th' in
  fun ax tm ->
    try let th = tryfind (find_redefinition tm) (!the_recursive_definitions) in
        warn true "Benign redefinition of recursive function"; th
    with Failure _ ->
    let rawcls = conjuncts tm in
    let spcls = map (snd o strip_forall) rawcls in
    let lpats = map (strip_comb o lhand) spcls in
    let ufns = itlist (insert o fst) lpats [] in
    let fvs = map (fun t -> subtract (frees t) ufns) rawcls in
    let gcls = map2 (curry list_mk_forall) fvs rawcls in
    let eth = prove_recursive_functions_exist ax (list_mk_conj gcls) in
    let evs,bod = strip_exists(concl eth) in
    let dth = new_specification (map (fst o dest_var) evs) eth in
    let dths = map2 SPECL fvs (CONJUNCTS dth) in
    let th = end_itlist CONJ dths in
    the_recursive_definitions := th::(!the_recursive_definitions); th;;
