(* ========================================================================= *)
(* Tools for defining quotient types and lifting first order theorems.       *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "thecops.ml";;

(* ------------------------------------------------------------------------- *)
(* Given a type name "ty" and a curried binary relation R, this defines      *)
(* a new type "ty" of R-equivalence classes. The abstraction and             *)
(* representation functions for the new type are called "mk_ty" and          *)
(* "dest_ty". The type bijections (after beta-conversion) are returned:      *)
(*                                                                           *)
(*             |- mk_ty (dest_ty a) = a                                      *)
(*                                                                           *)
(*             |- (?x. r = R x) <=> (dest_ty (mk_ty r) = r)                  *)
(* ------------------------------------------------------------------------- *)

let define_quotient_type =
  fun tyname (absname,repname) eqv ->
    let ty = hd(snd(dest_type(type_of eqv))) in
    let pty = mk_fun_ty ty bool_ty in
    let s = mk_var("s",pty) and x = mk_var("x",ty) in
    let eqvx = mk_comb(eqv,x) in
    let pred = mk_abs(s,mk_exists(x,mk_eq(s,eqvx))) in
    let th0 = BETA_CONV(mk_comb(pred,eqvx)) in
    let th1 = EXISTS(rand(concl th0),x) (REFL eqvx) in
    let th2 = EQ_MP (SYM th0) th1 in
    let abs,rep = new_basic_type_definition tyname (absname,repname) th2 in
    abs,CONV_RULE(LAND_CONV BETA_CONV) rep;;

(* ------------------------------------------------------------------------- *)
(* Given a welldefinedness theorem for a curried function f, of the form:    *)
(*                                                                           *)
(* |- !x1 x1' .. xn xn'. (x1 == x1') /\ ... /\ (xn == xn')                   *)
(*                       ==> (f x1 .. xn == f x1' .. f nx')                  *)
(*                                                                           *)
(* where each "==" is either equality or some fixed binary relation R, a     *)
(* new operator called "opname" is introduced which lifts "f" up to the      *)
(* R-equivalence classes. Two theorems are returned: the actual definition   *)
(* and a useful consequence for lifting theorems.                            *)
(*                                                                           *)
(* The function also needs the second (more complicated) type bijection, and *)
(* the reflexivity and transitivity (not symmetry!) of the equivalence       *)
(* relation. The use also gives a name for the new function.                 *)
(* ------------------------------------------------------------------------- *)

let lift_function =
  let SELECT_LEMMA = prove
   (`!x:A. (@y. x = y) = x`,
    GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [EQ_SYM_EQ] THEN
    MATCH_ACCEPT_TAC SELECT_REFL) in
  fun tybij2 ->
    let tybl,tybr = dest_comb(concl tybij2) in
    let eqvx = rand(body(rand(rand tybl))) in
    let eqv,xtm = dest_comb eqvx in
    let dmr,rtm = dest_eq tybr in
    let dest,mrt = dest_comb dmr in
    let mk = rator mrt in
    let ety = type_of mrt in
    fun (refl_th,trans_th) fname wth ->
      let wtm = repeat (snd o dest_forall) (concl wth) in
      let wfvs = frees wtm in
      let hyps,con = try (conjuncts F_F I) (dest_imp wtm)
                     with Failure _ -> [],wtm in
      let eqs,rels = partition is_eq hyps in
      let rvs = map lhand rels in
      let qvs = map lhs eqs in
      let evs =
        variants wfvs (map (fun v -> mk_var(fst(dest_var v),ety)) rvs) in
      let mems = map2 (fun rv ev -> mk_comb(mk_comb(dest,ev),rv)) rvs evs in
      let lcon,rcon = dest_comb con in
      let u = variant (evs @ wfvs) (mk_var("u",type_of rcon)) in
      let ucon = mk_comb(lcon,u) in
      let dbod = list_mk_conj(ucon::mems) in
      let detm = list_mk_exists(rvs,dbod) in
      let datm = mk_abs(u,detm) in
      let def =
        if is_eq con then list_mk_icomb "@" [datm] else mk_comb(mk,datm) in
      let newargs = map
        (fun e -> try lhs e with Failure _ -> assoc (lhand e) (zip rvs evs)) hyps in
      let rdef = list_mk_abs(newargs,def) in
      let ldef = mk_var(fname,type_of rdef) in
      let dth = new_definition(mk_eq(ldef,rdef)) in
      let eth = rev_itlist
        (fun v th -> CONV_RULE(RAND_CONV BETA_CONV) (AP_THM th v))
        newargs dth in
      let targs = map (fun v -> mk_comb(mk,mk_comb(eqv,v))) rvs in
      let dme_th =
        let th = INST [eqvx,rtm] tybij2 in
        EQ_MP th (EXISTS(lhs(concl th),xtm) (REFL eqvx)) in
      let ith = INST (zip targs evs) eth in
      let jth = SUBS (map (fun v -> INST[v,xtm] dme_th) rvs) ith in
      let apop,uxtm = dest_comb(rand(concl jth)) in
      let extm = body uxtm in
      let evs,bod = strip_exists extm in
      let th1 = ASSUME bod in
      let th2 =
        if evs = [] then th1 else
        let th2a,th2b = CONJ_PAIR th1 in
        let ethlist = CONJUNCTS th2b @ map REFL qvs in
        let th2c = end_itlist CONJ (map
          (fun v -> find ((=) (lhand v) o lhand o concl) ethlist) hyps) in
        let th2d = MATCH_MP wth th2c in
        let th2e = try TRANS th2d th2a
                   with Failure _ -> MATCH_MP trans_th (CONJ th2d th2a) in
        itlist SIMPLE_CHOOSE evs th2e in
      let th3 = ASSUME(concl th2) in
      let th4 = end_itlist CONJ (th3::(map (C SPEC refl_th) rvs)) in
      let th5 = itlist SIMPLE_EXISTS evs (ASSUME bod) in
      let th6 = MATCH_MP (DISCH_ALL th5) th4 in
      let th7 = IMP_ANTISYM_RULE (DISCH_ALL th2) (DISCH_ALL th6) in
      let th8 = TRANS jth (AP_TERM apop (ABS u th7)) in
      let fconv = if is_eq con then REWR_CONV SELECT_LEMMA
                  else RAND_CONV ETA_CONV in
      let th9 = CONV_RULE (RAND_CONV fconv) th8 in
      eth,GSYM th9;;

(* ------------------------------------------------------------------------- *)
(* Lifts a theorem. This can be done by higher order rewriting alone.        *)
(*                                                                           *)
(* NB! All and only the first order variables must be bound by quantifiers.  *)
(* ------------------------------------------------------------------------- *)

let lift_theorem =
  let pth = prove
   (`(!x:Repty. R x x) /\
     (!x y. R x y <=> R y x) /\
     (!x y z. R x y /\ R y z ==> R x z) /\
     (!a. mk(dest a) = a) /\
     (!r. (?x. r = R x) <=> (dest(mk r) = r))
     ==> (!x y. R x y <=> (mk(R x) = mk(R y))) /\
         (!P. (!x. P(mk(R x))) <=> (!x. P x)) /\
         (!P. (?x. P(mk(R x))) <=> (?x. P x)) /\
         (!x:Absty. mk(R((@)(dest x))) = x)`,
    STRIP_TAC THEN
    SUBGOAL_THEN
     `!x y. (mk((R:Repty->Repty->bool) x):Absty = mk(R y)) <=> (R x = R y)`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(a /\ b /\ c) /\ (b ==> a ==> d)
                       ==> a /\ b /\ c /\ d`) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REPEAT(DISCH_THEN(fun th -> REWRITE_TAC[GSYM th])) THEN
    X_GEN_TAC `x:Repty` THEN
    SUBGOAL_THEN `dest(mk((R:Repty->Repty->bool) x):Absty) = R x`
    SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [th]) THEN
    CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[]) in
  fun tybij (refl_th,sym_th,trans_th) ->
    let tybij1 = GEN_ALL (fst tybij)
    and tybij2 = GEN_ALL (snd tybij) in
    let cth = end_itlist CONJ [refl_th; sym_th; trans_th; tybij1; tybij2] in
    let ith = MATCH_MP pth cth in
    fun trths ->
      REWRITE_RULE (ith::trths);;
