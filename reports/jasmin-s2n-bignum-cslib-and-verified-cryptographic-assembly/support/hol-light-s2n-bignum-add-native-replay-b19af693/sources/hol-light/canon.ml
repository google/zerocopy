(* ========================================================================= *)
(* Reasonably efficient conversions for various canonical forms.             *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "trivia.ml";;

(* ------------------------------------------------------------------------- *)
(* Pre-simplification.                                                       *)
(* ------------------------------------------------------------------------- *)

let PRESIMP_CONV =
  GEN_REWRITE_CONV TOP_DEPTH_CONV
   [NOT_CLAUSES; AND_CLAUSES; OR_CLAUSES; IMP_CLAUSES; EQ_CLAUSES;
    FORALL_SIMP; EXISTS_SIMP; EXISTS_OR_THM; FORALL_AND_THM;
    LEFT_EXISTS_AND_THM; RIGHT_EXISTS_AND_THM;
    LEFT_FORALL_OR_THM; RIGHT_FORALL_OR_THM];;

(* ------------------------------------------------------------------------- *)
(* ACI rearrangements of conjunctions and disjunctions. This is much faster  *)
(* than AC xxx_ACI on large problems, as well as being more controlled.      *)
(* ------------------------------------------------------------------------- *)

let CONJ_ACI_RULE =
  let rec mk_fun th fn =
    let tm = concl th in
    if is_conj tm then
      let th1,th2 = CONJ_PAIR th in
      mk_fun th1 (mk_fun th2 fn)
    else (tm |-> th) fn
  and use_fun fn tm =
    if is_conj tm then
      let l,r = dest_conj tm in CONJ (use_fun fn l) (use_fun fn r)
    else apply fn tm in
  fun fm ->
    let p,p' = dest_eq fm in
    if p = p' then REFL p else
    let th = use_fun (mk_fun (ASSUME p) undefined) p'
    and th' = use_fun (mk_fun (ASSUME p') undefined) p in
    IMP_ANTISYM_RULE (DISCH_ALL th) (DISCH_ALL th');;

let DISJ_ACI_RULE =
  let pth_left = UNDISCH(TAUT `~(a \/ b) ==> ~a`)
  and pth_right = UNDISCH(TAUT `~(a \/ b) ==> ~b`)
  and pth = repeat UNDISCH (TAUT `~a ==> ~b ==> ~(a \/ b)`)
  and pth_neg = UNDISCH(TAUT `(~a <=> ~b) ==> (a <=> b)`)
  and a_tm = `a:bool` and b_tm = `b:bool` in
  let NOT_DISJ_PAIR th =
    let p,q = dest_disj(rand(concl th)) in
    let ilist = [p,a_tm; q,b_tm] in
    PROVE_HYP th (INST ilist pth_left),
    PROVE_HYP th (INST ilist pth_right)
  and NOT_DISJ th1 th2 =
    let th3 = INST [rand(concl th1),a_tm; rand(concl th2),b_tm] pth in
    PROVE_HYP th1 (PROVE_HYP th2 th3) in
  let rec mk_fun th fn =
    let tm = rand(concl th) in
    if is_disj tm then
      let th1,th2 = NOT_DISJ_PAIR th in
      mk_fun th1 (mk_fun th2 fn)
    else (tm |-> th) fn
  and use_fun fn tm =
    if is_disj tm then
      let l,r = dest_disj tm in NOT_DISJ (use_fun fn l) (use_fun fn r)
    else apply fn tm in
  fun fm ->
    let p,p' = dest_eq fm in
    if p = p' then REFL p else
    let th = use_fun (mk_fun (ASSUME(mk_neg p)) undefined) p'
    and th' = use_fun (mk_fun (ASSUME(mk_neg p')) undefined) p in
    let th1 = IMP_ANTISYM_RULE (DISCH_ALL th) (DISCH_ALL th') in
    PROVE_HYP th1 (INST [p,a_tm; p',b_tm] pth_neg);;

(* ------------------------------------------------------------------------- *)
(* Order canonically, right-associate and remove duplicates.                 *)
(* ------------------------------------------------------------------------- *)

let CONJ_CANON_CONV tm =
  let tm' = list_mk_conj(setify(conjuncts tm)) in
  CONJ_ACI_RULE(mk_eq(tm,tm'));;

let DISJ_CANON_CONV tm =
  let tm' = list_mk_disj(setify(disjuncts tm)) in
  DISJ_ACI_RULE(mk_eq(tm,tm'));;

(* ------------------------------------------------------------------------- *)
(* General NNF conversion. The user supplies some conversion to be applied   *)
(* to atomic formulas.                                                       *)
(*                                                                           *)
(* "Iff"s are split conjunctively or disjunctively according to the flag     *)
(* argument (conjuctively = true) until a universal quantifier (modulo       *)
(* current parity) is passed; after that they are split conjunctively. This  *)
(* is appropriate when the result is passed to a disjunctive splitter        *)
(* followed by a clausal form inner core, such as MESON.                     *)
(*                                                                           *)
(* To avoid some duplicate computation, this function will in general        *)
(* enter a recursion where it simultaneously computes NNF representations    *)
(* for "p" and "~p", so the user needs to supply an atomic "conversion"      *)
(* that does the same.                                                       *)
(* ------------------------------------------------------------------------- *)

let (GEN_NNF_CONV:bool->conv*(term->thm*thm)->conv) =
  let and_tm = `(/\)` and or_tm = `(\/)` and not_tm = `(~)`
  and pth_not_not = TAUT `~ ~ p = p`
  and pth_not_and = TAUT `~(p /\ q) <=> ~p \/ ~q`
  and pth_not_or = TAUT `~(p \/ q) <=> ~p /\ ~q`
  and pth_imp = TAUT `p ==> q <=> ~p \/ q`
  and pth_not_imp = TAUT `~(p ==> q) <=> p /\ ~q`
  and pth_eq = TAUT `(p <=> q) <=> p /\ q \/ ~p /\ ~q`
  and pth_not_eq = TAUT `~(p <=> q) <=> p /\ ~q \/ ~p /\ q`
  and pth_eq' = TAUT `(p <=> q) <=> (p \/ ~q) /\ (~p \/ q)`
  and pth_not_eq' = TAUT `~(p <=> q) <=> (p \/ q) /\ (~p \/ ~q)`
  and [pth_not_forall; pth_not_exists; pth_not_exu] =
   (CONJUNCTS o prove)
   (`(~((!) P) <=> ?x:A. ~(P x)) /\
     (~((?) P) <=> !x:A. ~(P x)) /\
     (~((?!) P) <=> (!x:A. ~(P x)) \/ ?x y. P x /\ P y /\ ~(y = x))`,
    REPEAT CONJ_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV) [GSYM ETA_AX] THEN
    REWRITE_TAC[NOT_EXISTS_THM; NOT_FORALL_THM; EXISTS_UNIQUE_DEF;
                DE_MORGAN_THM; NOT_IMP] THEN
    REWRITE_TAC[CONJ_ASSOC; EQ_SYM_EQ])
  and pth_exu = prove
   (`((?!) P) <=> (?x:A. P x) /\ !x y. ~(P x) \/ ~(P y) \/ (y = x)`,
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
    REWRITE_TAC[EXISTS_UNIQUE_DEF; TAUT `a /\ b ==> c <=> ~a \/ ~b \/ c`] THEN
    REWRITE_TAC[EQ_SYM_EQ])
  and p_tm = `p:bool` and q_tm = `q:bool` in
  let rec NNF_DCONV cf baseconvs tm =
    match tm with
      Comb(Comb(Const("/\\",_),l),r) ->
          let th_lp,th_ln = NNF_DCONV cf baseconvs l
          and th_rp,th_rn = NNF_DCONV cf baseconvs r in
          MK_COMB(AP_TERM and_tm th_lp,th_rp),
          TRANS (INST [l,p_tm; r,q_tm] pth_not_and)
                (MK_COMB(AP_TERM or_tm th_ln,th_rn))
    | Comb(Comb(Const("\\/",_),l),r) ->
          let th_lp,th_ln = NNF_DCONV cf baseconvs l
          and th_rp,th_rn = NNF_DCONV cf baseconvs r in
          MK_COMB(AP_TERM or_tm th_lp,th_rp),
          TRANS (INST [l,p_tm; r,q_tm] pth_not_or)
                (MK_COMB(AP_TERM and_tm th_ln,th_rn))
    | Comb(Comb(Const("==>",_),l),r) ->
          let th_lp,th_ln = NNF_DCONV cf baseconvs l
          and th_rp,th_rn = NNF_DCONV cf baseconvs r in
          TRANS (INST [l,p_tm; r,q_tm] pth_imp)
                (MK_COMB(AP_TERM or_tm th_ln,th_rp)),
          TRANS (INST [l,p_tm; r,q_tm] pth_not_imp)
                (MK_COMB(AP_TERM and_tm th_lp,th_rn))
    | Comb(Comb(Const("=",Tyapp("fun",Tyapp("bool",_)::_)),l),r) ->
          let th_lp,th_ln = NNF_DCONV cf baseconvs l
          and th_rp,th_rn = NNF_DCONV cf baseconvs r in
          if cf then
            TRANS (INST [l,p_tm; r,q_tm] pth_eq')
                  (MK_COMB(AP_TERM and_tm (MK_COMB(AP_TERM or_tm th_lp,th_rn)),
                           MK_COMB(AP_TERM or_tm th_ln,th_rp))),
            TRANS (INST [l,p_tm; r,q_tm] pth_not_eq')
                  (MK_COMB(AP_TERM and_tm (MK_COMB(AP_TERM or_tm th_lp,th_rp)),
                           MK_COMB(AP_TERM or_tm th_ln,th_rn)))
          else
            TRANS (INST [l,p_tm; r,q_tm] pth_eq)
                  (MK_COMB(AP_TERM or_tm (MK_COMB(AP_TERM and_tm th_lp,th_rp)),
                           MK_COMB(AP_TERM and_tm th_ln,th_rn))),
            TRANS (INST [l,p_tm; r,q_tm] pth_not_eq)
                  (MK_COMB(AP_TERM or_tm (MK_COMB(AP_TERM and_tm th_lp,th_rn)),
                           MK_COMB(AP_TERM and_tm th_ln,th_rp)))
    | Comb(Const("!",Tyapp("fun",Tyapp("fun",ty::_)::_)) as q,
           (Abs(x,t) as bod)) ->
          let th_p,th_n = NNF_DCONV true baseconvs t in
          AP_TERM q (ABS x th_p),
          let th1 = INST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                         (INST_TYPE [ty,aty] pth_not_forall)
          and th2 = TRANS (AP_TERM not_tm (BETA(mk_comb(bod,x)))) th_n in
          TRANS th1 (MK_EXISTS x th2)
    | Comb(Const("?",Tyapp("fun",Tyapp("fun",ty::_)::_)) as q,
           (Abs(x,t) as bod)) ->
          let th_p,th_n = NNF_DCONV cf baseconvs t in
          AP_TERM q (ABS x th_p),
          let th1 = INST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                         (INST_TYPE [ty,aty] pth_not_exists)
          and th2 = TRANS (AP_TERM not_tm (BETA(mk_comb(bod,x)))) th_n in
          TRANS th1 (MK_FORALL x th2)
    | Comb(Const("?!",Tyapp("fun",Tyapp("fun",ty::_)::_)),
           (Abs(x,t) as bod)) ->
          let y = variant (x::frees t) x
          and th_p,th_n = NNF_DCONV cf baseconvs t in
          let eq = mk_eq(y,x) in
          let eth_p,eth_n = baseconvs eq
          and bth = BETA (mk_comb(bod,x))
          and bth' = BETA_CONV(mk_comb(bod,y)) in
          let th_p' = INST [y,x] th_p and th_n' = INST [y,x] th_n in
          let th1 = INST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                         (INST_TYPE [ty,aty] pth_exu)
          and th1' = INST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                          (INST_TYPE [ty,aty] pth_not_exu)
          and th2 =
            MK_COMB(AP_TERM and_tm
                        (MK_EXISTS x (TRANS bth th_p)),
                    MK_FORALL x (MK_FORALL y
                     (MK_COMB(AP_TERM or_tm (TRANS (AP_TERM not_tm bth) th_n),
                              MK_COMB(AP_TERM or_tm
                                    (TRANS (AP_TERM not_tm bth') th_n'),
                                      eth_p)))))
          and th2' =
            MK_COMB(AP_TERM or_tm
                        (MK_FORALL x (TRANS (AP_TERM not_tm bth) th_n)),
                    MK_EXISTS x (MK_EXISTS y
                     (MK_COMB(AP_TERM and_tm (TRANS bth th_p),
                              MK_COMB(AP_TERM and_tm (TRANS bth' th_p'),
                                      eth_n))))) in
          TRANS th1 th2,TRANS th1' th2'
    | Comb(Const("~",_),t) ->
          let th1,th2 = NNF_DCONV cf baseconvs t in
          th2,TRANS (INST [t,p_tm] pth_not_not) th1
    | _ -> try baseconvs tm
           with Failure _ -> REFL tm,REFL(mk_neg tm) in
  let rec NNF_CONV cf (base1,base2 as baseconvs) tm =
    match tm with
      Comb(Comb(Const("/\\",_),l),r) ->
          let th_lp = NNF_CONV cf baseconvs l
          and th_rp = NNF_CONV cf baseconvs r in
          MK_COMB(AP_TERM and_tm th_lp,th_rp)
    | Comb(Comb(Const("\\/",_),l),r) ->
          let th_lp = NNF_CONV cf baseconvs l
          and th_rp = NNF_CONV cf baseconvs r in
          MK_COMB(AP_TERM or_tm th_lp,th_rp)
    | Comb(Comb(Const("==>",_),l),r) ->
          let th_ln = NNF_CONV' cf baseconvs l
          and th_rp = NNF_CONV cf baseconvs r in
          TRANS (INST [l,p_tm; r,q_tm] pth_imp)
                (MK_COMB(AP_TERM or_tm th_ln,th_rp))
    | Comb(Comb(Const("=",Tyapp("fun",Tyapp("bool",_)::_)),l),r) ->
          let th_lp,th_ln = NNF_DCONV cf base2 l
          and th_rp,th_rn = NNF_DCONV cf base2 r in
          if cf then
            TRANS (INST [l,p_tm; r,q_tm] pth_eq')
                  (MK_COMB(AP_TERM and_tm (MK_COMB(AP_TERM or_tm th_lp,th_rn)),
                           MK_COMB(AP_TERM or_tm th_ln,th_rp)))
          else
            TRANS (INST [l,p_tm; r,q_tm] pth_eq)
                  (MK_COMB(AP_TERM or_tm (MK_COMB(AP_TERM and_tm th_lp,th_rp)),
                           MK_COMB(AP_TERM and_tm th_ln,th_rn)))
    | Comb(Const("!",Tyapp("fun",Tyapp("fun",ty::_)::_)) as q,
           (Abs(x,t))) ->
          let th_p = NNF_CONV true baseconvs t in
          AP_TERM q (ABS x th_p)
    | Comb(Const("?",Tyapp("fun",Tyapp("fun",ty::_)::_)) as q,
           (Abs(x,t))) ->
          let th_p = NNF_CONV cf baseconvs t in
          AP_TERM q (ABS x th_p)
    | Comb(Const("?!",Tyapp("fun",Tyapp("fun",ty::_)::_)),
           (Abs(x,t) as bod)) ->
          let y = variant (x::frees t) x
          and th_p,th_n = NNF_DCONV cf base2 t in
          let eq = mk_eq(y,x) in
          let eth_p,eth_n = base2 eq
          and bth = BETA (mk_comb(bod,x))
          and bth' = BETA_CONV(mk_comb(bod,y)) in
          let th_n' = INST [y,x] th_n in
          let th1 = INST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                         (INST_TYPE [ty,aty] pth_exu)
          and th2 =
            MK_COMB(AP_TERM and_tm
                        (MK_EXISTS x (TRANS bth th_p)),
                    MK_FORALL x (MK_FORALL y
                     (MK_COMB(AP_TERM or_tm (TRANS (AP_TERM not_tm bth) th_n),
                              MK_COMB(AP_TERM or_tm
                                    (TRANS (AP_TERM not_tm bth') th_n'),
                                      eth_p))))) in
          TRANS th1 th2
    | Comb(Const("~",_),t) -> NNF_CONV' cf baseconvs t
    | _ -> try base1 tm with Failure _ -> REFL tm
  and NNF_CONV' cf (base1,base2 as baseconvs) tm =
    match tm with
      Comb(Comb(Const("/\\",_),l),r) ->
          let th_ln = NNF_CONV' cf baseconvs l
          and th_rn = NNF_CONV' cf baseconvs r in
          TRANS (INST [l,p_tm; r,q_tm] pth_not_and)
                (MK_COMB(AP_TERM or_tm th_ln,th_rn))
    | Comb(Comb(Const("\\/",_),l),r) ->
          let th_ln = NNF_CONV' cf baseconvs l
          and th_rn = NNF_CONV' cf baseconvs r in
          TRANS (INST [l,p_tm; r,q_tm] pth_not_or)
                (MK_COMB(AP_TERM and_tm th_ln,th_rn))
    | Comb(Comb(Const("==>",_),l),r) ->
          let th_lp = NNF_CONV cf baseconvs l
          and th_rn = NNF_CONV' cf baseconvs r in
          TRANS (INST [l,p_tm; r,q_tm] pth_not_imp)
                (MK_COMB(AP_TERM and_tm th_lp,th_rn))
    | Comb(Comb(Const("=",Tyapp("fun",Tyapp("bool",_)::_)),l),r) ->
          let th_lp,th_ln = NNF_DCONV cf base2 l
          and th_rp,th_rn = NNF_DCONV cf base2 r in
          if cf then
            TRANS (INST [l,p_tm; r,q_tm] pth_not_eq')
                  (MK_COMB(AP_TERM and_tm (MK_COMB(AP_TERM or_tm th_lp,th_rp)),
                           MK_COMB(AP_TERM or_tm th_ln,th_rn)))
          else
            TRANS (INST [l,p_tm; r,q_tm] pth_not_eq)
                  (MK_COMB(AP_TERM or_tm (MK_COMB(AP_TERM and_tm th_lp,th_rn)),
                           MK_COMB(AP_TERM and_tm th_ln,th_rp)))
    | Comb(Const("!",Tyapp("fun",Tyapp("fun",ty::_)::_)),
           (Abs(x,t) as bod)) ->
          let th_n = NNF_CONV' cf baseconvs t in
          let th1 = INST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                         (INST_TYPE [ty,aty] pth_not_forall)
          and th2 = TRANS (AP_TERM not_tm (BETA(mk_comb(bod,x)))) th_n in
          TRANS th1 (MK_EXISTS x th2)
    | Comb(Const("?",Tyapp("fun",Tyapp("fun",ty::_)::_)),
           (Abs(x,t) as bod)) ->
          let th_n = NNF_CONV' true baseconvs t in
          let th1 = INST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                         (INST_TYPE [ty,aty] pth_not_exists)
          and th2 = TRANS (AP_TERM not_tm (BETA(mk_comb(bod,x)))) th_n in
          TRANS th1 (MK_FORALL x th2)
    | Comb(Const("?!",Tyapp("fun",Tyapp("fun",ty::_)::_)),
           (Abs(x,t) as bod)) ->
          let y = variant (x::frees t) x
          and th_p,th_n = NNF_DCONV cf base2 t in
          let eq = mk_eq(y,x) in
          let eth_p,eth_n = base2 eq
          and bth = BETA (mk_comb(bod,x))
          and bth' = BETA_CONV(mk_comb(bod,y)) in
          let th_p' = INST [y,x] th_p in
          let th1' = INST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                          (INST_TYPE [ty,aty] pth_not_exu)
          and th2' =
            MK_COMB(AP_TERM or_tm
                        (MK_FORALL x (TRANS (AP_TERM not_tm bth) th_n)),
                    MK_EXISTS x (MK_EXISTS y
                     (MK_COMB(AP_TERM and_tm (TRANS bth th_p),
                              MK_COMB(AP_TERM and_tm (TRANS bth' th_p'),
                                      eth_n))))) in
          TRANS th1' th2'
    | Comb(Const("~",_),t) ->
          let th1 = NNF_CONV cf baseconvs t in
          TRANS (INST [t,p_tm] pth_not_not) th1
    | _ -> let tm' = mk_neg tm in try base1 tm' with Failure _ -> REFL tm' in
  NNF_CONV;;

(* ------------------------------------------------------------------------- *)
(* Some common special cases.                                                *)
(* ------------------------------------------------------------------------- *)

let NNF_CONV =
  (GEN_NNF_CONV false (ALL_CONV,fun t -> REFL t,REFL(mk_neg t)) :conv);;

let NNFC_CONV =
  (GEN_NNF_CONV true (ALL_CONV,fun t -> REFL t,REFL(mk_neg t)) :conv);;

(* ------------------------------------------------------------------------- *)
(* Skolemize a term already in NNF (doesn't matter if it's not prenex).      *)
(* ------------------------------------------------------------------------- *)

let SKOLEM_CONV =
  GEN_REWRITE_CONV TOP_DEPTH_CONV
   [EXISTS_OR_THM; LEFT_EXISTS_AND_THM; RIGHT_EXISTS_AND_THM;
    FORALL_AND_THM; LEFT_FORALL_OR_THM; RIGHT_FORALL_OR_THM;
    FORALL_SIMP; EXISTS_SIMP] THENC
  GEN_REWRITE_CONV REDEPTH_CONV
   [RIGHT_AND_EXISTS_THM;
    LEFT_AND_EXISTS_THM;
    OR_EXISTS_THM;
    RIGHT_OR_EXISTS_THM;
    LEFT_OR_EXISTS_THM;
    SKOLEM_THM];;

(* ------------------------------------------------------------------------- *)
(* Put a term already in NNF into prenex form.                               *)
(* ------------------------------------------------------------------------- *)

let PRENEX_CONV =
  GEN_REWRITE_CONV REDEPTH_CONV
   [AND_FORALL_THM; LEFT_AND_FORALL_THM; RIGHT_AND_FORALL_THM;
    LEFT_OR_FORALL_THM; RIGHT_OR_FORALL_THM;
    OR_EXISTS_THM; LEFT_OR_EXISTS_THM; RIGHT_OR_EXISTS_THM;
    LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM];;

(* ------------------------------------------------------------------------- *)
(* Weak and normal DNF conversion. The "weak" form gives a disjunction of    *)
(* conjunctions, but has no particular associativity at either level and     *)
(* may contain duplicates. The regular forms give canonical right-associate  *)
(* lists without duplicates, but do not remove subsumed disjuncts.           *)
(*                                                                           *)
(* In both cases the input term is supposed to be in NNF already. We do go   *)
(* inside quantifiers and transform their body, but don't move them.         *)
(* ------------------------------------------------------------------------- *)

let WEAK_DNF_CONV,DNF_CONV =
  let pth1 = TAUT `a /\ (b \/ c) <=> a /\ b \/ a /\ c`
  and pth2 = TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`
  and a_tm = `a:bool` and b_tm = `b:bool` and c_tm = `c:bool` in
  let rec distribute tm =
    match tm with
      Comb(Comb(Const("/\\",_),a),Comb(Comb(Const("\\/",_),b),c)) ->
          let th = INST [a,a_tm; b,b_tm; c,c_tm] pth1 in
          TRANS th (BINOP_CONV distribute (rand(concl th)))
    | Comb(Comb(Const("/\\",_),Comb(Comb(Const("\\/",_),a),b)),c) ->
          let th = INST [a,a_tm; b,b_tm; c,c_tm] pth2 in
          TRANS th (BINOP_CONV distribute (rand(concl th)))
    | _ -> REFL tm in
  let strengthen =
    DEPTH_BINOP_CONV `(\/)` CONJ_CANON_CONV THENC DISJ_CANON_CONV in
  let rec weakdnf tm =
    match tm with
      Comb(Const("!",_),Abs(_,_))
    | Comb(Const("?",_),Abs(_,_)) -> BINDER_CONV weakdnf tm
    | Comb(Comb(Const("\\/",_),_),_) -> BINOP_CONV weakdnf tm
    | Comb(Comb(Const("/\\",_) as op,l),r) ->
          let th = MK_COMB(AP_TERM op (weakdnf l),weakdnf r) in
          TRANS th (distribute(rand(concl th)))
    | _ -> REFL tm
  and substrongdnf tm =
    match tm with
      Comb(Const("!",_),Abs(_,_))
    | Comb(Const("?",_),Abs(_,_)) -> BINDER_CONV strongdnf tm
    | Comb(Comb(Const("\\/",_),_),_) -> BINOP_CONV substrongdnf tm
    | Comb(Comb(Const("/\\",_) as op,l),r) ->
          let th = MK_COMB(AP_TERM op (substrongdnf l),substrongdnf r) in
          TRANS th (distribute(rand(concl th)))
    | _ -> REFL tm
  and strongdnf tm =
    let th = substrongdnf tm in
    TRANS th (strengthen(rand(concl th))) in
  weakdnf,strongdnf;;

(* ------------------------------------------------------------------------- *)
(* Likewise for CNF.                                                         *)
(* ------------------------------------------------------------------------- *)

let WEAK_CNF_CONV,CNF_CONV =
  let pth1 = TAUT `a \/ (b /\ c) <=> (a \/ b) /\ (a \/ c)`
  and pth2 = TAUT `(a /\ b) \/ c <=> (a \/ c) /\ (b \/ c)`
  and a_tm = `a:bool` and b_tm = `b:bool` and c_tm = `c:bool` in
  let rec distribute tm =
    match tm with
      Comb(Comb(Const("\\/",_),a),Comb(Comb(Const("/\\",_),b),c)) ->
          let th = INST [a,a_tm; b,b_tm; c,c_tm] pth1 in
          TRANS th (BINOP_CONV distribute (rand(concl th)))
    | Comb(Comb(Const("\\/",_),Comb(Comb(Const("/\\",_),a),b)),c) ->
          let th = INST [a,a_tm; b,b_tm; c,c_tm] pth2 in
          TRANS th (BINOP_CONV distribute (rand(concl th)))
    | _ -> REFL tm in
  let strengthen =
    DEPTH_BINOP_CONV `(/\)` DISJ_CANON_CONV THENC CONJ_CANON_CONV in
  let rec weakcnf tm =
    match tm with
      Comb(Const("!",_),Abs(_,_))
    | Comb(Const("?",_),Abs(_,_)) -> BINDER_CONV weakcnf tm
    | Comb(Comb(Const("/\\",_),_),_) -> BINOP_CONV weakcnf tm
    | Comb(Comb(Const("\\/",_) as op,l),r) ->
          let th = MK_COMB(AP_TERM op (weakcnf l),weakcnf r) in
          TRANS th (distribute(rand(concl th)))
    | _ -> REFL tm
  and substrongcnf tm =
    match tm with
      Comb(Const("!",_),Abs(_,_))
    | Comb(Const("?",_),Abs(_,_)) -> BINDER_CONV strongcnf tm
    | Comb(Comb(Const("/\\",_),_),_) -> BINOP_CONV substrongcnf tm
    | Comb(Comb(Const("\\/",_) as op,l),r) ->
          let th = MK_COMB(AP_TERM op (substrongcnf l),substrongcnf r) in
          TRANS th (distribute(rand(concl th)))
    | _ -> REFL tm
  and strongcnf tm =
    let th = substrongcnf tm in
    TRANS th (strengthen(rand(concl th))) in
  weakcnf,strongcnf;;

(* ------------------------------------------------------------------------- *)
(* Simply right-associate w.r.t. a binary operator.                          *)
(* ------------------------------------------------------------------------- *)

let ASSOC_CONV th =
  let th' = SYM(SPEC_ALL th) in
  let opx,yopz = dest_comb(rhs(concl th')) in
  let op,x = dest_comb opx in
  let y = lhand yopz and z = rand yopz in
  let rec distrib tm =
    match tm with
      Comb(Comb(op',Comb(Comb(op'',p),q)),r) when op' = op && op'' = op ->
          let th1 = INST [p,x; q,y; r,z] th' in
          let l,r' = dest_comb(rand(concl th1)) in
          let th2 = AP_TERM l (distrib r') in
          let th3 = distrib(rand(concl th2)) in
          TRANS th1 (TRANS th2 th3)
    | _ -> REFL tm in
  let rec assoc tm =
    match tm with
      Comb(Comb(op',p) as l,q) when op' = op ->
          let th = AP_TERM l (assoc q) in
          TRANS th (distrib(rand(concl th)))
    | _ -> REFL tm in
  assoc;;

(* ------------------------------------------------------------------------- *)
(* Eliminate select terms from a goal.                                       *)
(* ------------------------------------------------------------------------- *)

let SELECT_ELIM_TAC =
  let SELECT_ELIM_CONV =
    let SELECT_ELIM_THM =
      let pth = prove
       (`(P:A->bool)((@) P) <=> (?) P`,
        REWRITE_TAC[EXISTS_THM] THEN BETA_TAC THEN REFL_TAC)
      and ptm = `P:A->bool` in
      fun tm -> let stm,atm = dest_comb tm in
                if is_const stm && fst(dest_const stm) = "@" then
                 CONV_RULE(LAND_CONV BETA_CONV)
                   (PINST [type_of(bndvar atm),aty] [atm,ptm] pth)
                else failwith "SELECT_ELIM_THM: not a select-term" in
    fun tm ->
      PURE_REWRITE_CONV (map SELECT_ELIM_THM (find_terms is_select tm)) tm in
  let SELECT_ELIM_ICONV =
    let SELECT_AX_THM =
      let pth = ISPEC `P:A->bool` SELECT_AX
      and ptm = `P:A->bool` in
      fun tm -> let stm,atm = dest_comb tm in
                if is_const stm && fst(dest_const stm) = "@" then
                  let fvs = frees atm in
                  let th1 = PINST [type_of(bndvar atm),aty] [atm,ptm] pth in
                  let th2 = CONV_RULE(BINDER_CONV (BINOP_CONV BETA_CONV)) th1 in
                  GENL fvs th2
                else failwith "SELECT_AX_THM: not a select-term" in
    let SELECT_ELIM_ICONV tm =
      let t = find_term is_select tm in
      let th1 = SELECT_AX_THM t in
      let itm = mk_imp(concl th1,tm) in
      let th2 = DISCH_ALL (MP (ASSUME itm) th1) in
      let fvs = frees t in
      let fty = itlist (mk_fun_ty o type_of) fvs (type_of t) in
      let fn = genvar fty
      and atm = list_mk_abs(fvs,t) in
      let rawdef = mk_eq(fn,atm) in
      let def = GENL fvs (SYM(RIGHT_BETAS fvs (ASSUME rawdef))) in
      let th3 = PURE_REWRITE_CONV[def] (lhand(concl th2)) in
      let gtm = mk_forall(fn,rand(concl th3)) in
      let th4 = EQ_MP (SYM th3) (SPEC fn (ASSUME gtm)) in
      let th5 = IMP_TRANS (DISCH gtm th4) th2 in
      MP (INST [atm,fn] (DISCH rawdef th5)) (REFL atm) in
    let rec SELECT_ELIMS_ICONV tm =
      try let th = SELECT_ELIM_ICONV tm in
          let tm' = lhand(concl th) in
          IMP_TRANS (SELECT_ELIMS_ICONV tm') th
      with Failure _ -> DISCH tm (ASSUME tm) in
    SELECT_ELIMS_ICONV in
  CONV_TAC SELECT_ELIM_CONV THEN W(MATCH_MP_TAC o SELECT_ELIM_ICONV o snd);;

(* ------------------------------------------------------------------------- *)
(* Eliminate all lambda-terms except those part of quantifiers.              *)
(* ------------------------------------------------------------------------- *)

let LAMBDA_ELIM_CONV =
  let HALF_MK_ABS_CONV =
    let pth = prove
     (`(s = \x. t x) <=> (!x. s x = t x)`,
      REWRITE_TAC[FUN_EQ_THM]) in
    let rec conv vs tm =
      if vs = [] then REFL tm else
      (GEN_REWRITE_CONV I [pth] THENC BINDER_CONV(conv (tl vs))) tm in
    conv in
  let rec find_lambda tm =
    if is_abs tm then tm
    else if is_var tm || is_const tm then failwith "find_lambda"
    else if is_abs tm then tm else
    if is_forall tm || is_exists tm || is_uexists tm
    then find_lambda (body(rand tm)) else
    let l,r = dest_comb tm in
    try find_lambda l with Failure _ -> find_lambda r in
  let rec ELIM_LAMBDA conv tm =
    try conv tm with Failure _ ->
    if is_abs tm then ABS_CONV (ELIM_LAMBDA conv) tm
    else if is_var tm || is_const tm then REFL tm else
    if is_forall tm || is_exists tm || is_uexists tm
    then BINDER_CONV (ELIM_LAMBDA conv) tm
    else COMB_CONV (ELIM_LAMBDA conv) tm in
  let APPLY_PTH =
    let pth = prove
     (`(!a. (a = c) ==> (P = Q a)) ==> (P <=> !a. (a = c) ==> Q a)`,
      SIMP_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL]) in
    MATCH_MP pth in
  let LAMB1_CONV tm =
    let atm = find_lambda tm in
    let v,bod = dest_abs atm in
    let vs = frees atm in
    let vs' = vs @ [v] in
    let aatm = list_mk_abs(vs,atm) in
    let f = genvar(type_of aatm) in
    let eq = mk_eq(f,aatm) in
    let th1 = SYM(RIGHT_BETAS vs (ASSUME eq)) in
    let th2 = ELIM_LAMBDA(GEN_REWRITE_CONV I [th1]) tm in
    let th3 = APPLY_PTH (GEN f (DISCH_ALL th2)) in
    CONV_RULE(RAND_CONV(BINDER_CONV(LAND_CONV (HALF_MK_ABS_CONV vs')))) th3 in
  let rec conv tm =
    try (LAMB1_CONV THENC conv) tm with Failure _ -> REFL tm in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Eliminate conditionals; CONDS_ELIM_CONV aims for disjunctive splitting,   *)
(* for refutation procedures, and CONDS_CELIM_CONV for conjunctive.          *)
(* Both switch modes "sensibly" when going through a quantifier.             *)
(* ------------------------------------------------------------------------- *)

let CONDS_ELIM_CONV,CONDS_CELIM_CONV =
  let th_cond = prove
   (`((b <=> F) ==> x = x0) /\ ((b <=> T) ==> x = x1)
     ==> x = (b /\ x1 \/ ~b /\ x0)`,
    BOOL_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[])
  and th_cond' = prove
   (`((b <=> F) ==> x = x0) /\ ((b <=> T) ==> x = x1)
     ==> x = ((~b \/ x1) /\ (b \/ x0))`,
    BOOL_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[])
  and propsimps = basic_net()
  and false_tm = `F` and true_tm = `T` in
  let match_th = MATCH_MP th_cond and match_th' = MATCH_MP th_cond'
  and propsimp_conv = DEPTH_CONV(REWRITES_CONV propsimps)
  and proptsimp_conv =
    let cnv = TRY_CONV(REWRITES_CONV propsimps) in
    BINOP_CONV cnv THENC cnv in
  let rec find_conditional fvs tm =
    match tm with
      Comb(s,t) ->
        if is_cond tm && intersect (frees(lhand s)) fvs = [] then tm
        else (try (find_conditional fvs s)
              with Failure _ -> find_conditional fvs t)
    | Abs(x,t) -> find_conditional (x::fvs) t
    | _ -> failwith "find_conditional" in
  let rec CONDS_ELIM_CONV dfl tm =
    try let t = find_conditional [] tm in
        let p = lhand(rator t) in
        let th_new =
          if p = false_tm || p = true_tm then propsimp_conv tm else
          let asm_0 = mk_eq(p,false_tm) and asm_1 = mk_eq(p,true_tm) in
          let simp_0 = net_of_thm false (ASSUME asm_0) propsimps
          and simp_1 = net_of_thm false (ASSUME asm_1) propsimps in
          let th_0 = DISCH asm_0 (DEPTH_CONV(REWRITES_CONV simp_0) tm)
          and th_1 = DISCH asm_1 (DEPTH_CONV(REWRITES_CONV simp_1) tm) in
          let th_2 = CONJ th_0 th_1 in
          let th_3 = if dfl then match_th th_2 else match_th' th_2 in
          TRANS th_3 (proptsimp_conv(rand(concl th_3))) in
        CONV_RULE (RAND_CONV (CONDS_ELIM_CONV dfl)) th_new
    with Failure _ ->
    if is_neg tm then
       RAND_CONV (CONDS_ELIM_CONV (not dfl)) tm
    else if is_conj tm || is_disj tm then
       BINOP_CONV (CONDS_ELIM_CONV dfl) tm
    else if is_imp tm || is_iff tm then
       COMB2_CONV (RAND_CONV (CONDS_ELIM_CONV (not dfl)))
                  (CONDS_ELIM_CONV dfl) tm
    else if is_forall tm then
         BINDER_CONV (CONDS_ELIM_CONV false) tm
    else if is_exists tm || is_uexists tm then
         BINDER_CONV (CONDS_ELIM_CONV true) tm
    else REFL tm in
  CONDS_ELIM_CONV true,CONDS_ELIM_CONV false;;

(* ------------------------------------------------------------------------- *)
(* Fix up all head arities to be consistent, in "first order logic" style.   *)
(* Applied to the assumptions (not conclusion) in a goal.                    *)
(* ------------------------------------------------------------------------- *)

let ASM_FOL_TAC =
  let rec get_heads lconsts tm (cheads,vheads as sofar) =
    try let v,bod = dest_forall tm in
        get_heads (subtract lconsts [v]) bod sofar
    with Failure _ -> try
        let l,r = try dest_conj tm with Failure _ -> dest_disj tm in
        get_heads lconsts l (get_heads lconsts r sofar)
    with Failure _ -> try
        let tm' = dest_neg tm in
        get_heads lconsts tm' sofar
    with Failure _ ->
        let hop,args = strip_comb tm in
        let len = length args in
        let newheads =
          if is_const hop || mem hop lconsts
          then (insert (hop,len) cheads,vheads)
          else if len > 0 then (cheads,insert (hop,len) vheads) else sofar in
        itlist (get_heads lconsts) args newheads in
  let get_thm_heads th sofar =
    get_heads (freesl(hyp th)) (concl th) sofar in
  let APP_CONV =
    let th = prove
     (`!(f:A->B) x. f x = I f x`,
      REWRITE_TAC[I_THM]) in
    REWR_CONV th in
  let rec APP_N_CONV n tm =
    if n = 1 then APP_CONV tm
    else (RATOR_CONV (APP_N_CONV (n - 1)) THENC APP_CONV) tm in
  let rec FOL_CONV hddata tm =
    if is_forall tm then BINDER_CONV (FOL_CONV hddata) tm
    else if is_conj tm || is_disj tm then BINOP_CONV (FOL_CONV hddata) tm else
    let op,args = strip_comb tm in
    let th = rev_itlist (C (curry MK_COMB))
                        (map (FOL_CONV hddata) args) (REFL op) in
    let tm' = rand(concl th) in
    let n = try length args - assoc op hddata with Failure _ -> 0 in
    if n = 0 then th
    else TRANS th (APP_N_CONV n tm') in
  let GEN_FOL_CONV (cheads,vheads) =
    let hddata =
      if vheads = [] then
        let hops = setify (map fst cheads) in
        let getmin h =
          let ns = mapfilter
            (fun (k,n) -> if k = h then n else fail()) cheads in
          if length ns < 2 then fail() else h,end_itlist min ns in
        mapfilter getmin hops
      else
        map (fun t -> if is_const t && fst(dest_const t) = "="
                      then t,2 else t,0)
            (setify (map fst (vheads @ cheads))) in
    FOL_CONV hddata in
  fun (asl,w as gl) ->
    let headsp = itlist (get_thm_heads o snd) asl ([],[]) in
    RULE_ASSUM_TAC(CONV_RULE(GEN_FOL_CONV headsp)) gl;;

(* ------------------------------------------------------------------------- *)
(* Depth conversion to apply at "atomic" formulas in "first-order" term.     *)
(* ------------------------------------------------------------------------- *)

let rec PROP_ATOM_CONV conv tm =
  match tm with
    Comb((Const("!",_) | Const("?",_) | Const("?!",_)),Abs(_,_))
      -> BINDER_CONV (PROP_ATOM_CONV conv) tm
  | Comb(Comb
     ((Const("/\\",_) | Const("\\/",_) | Const("==>",_) |
       (Const("=",Tyapp("fun",[Tyapp("bool",[]);_])))),_),_)
        -> BINOP_CONV (PROP_ATOM_CONV conv) tm
  | Comb(Const("~",_),_) -> RAND_CONV (PROP_ATOM_CONV conv) tm
  | _ -> TRY_CONV conv tm;;
