(* ========================================================================= *)
(* Extensional, classical reasoning with AC starts now!                      *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "ind_defs.ml";;

(* ------------------------------------------------------------------------- *)
(* Eta-axiom, corresponding conversion, and extensionality.                  *)
(* ------------------------------------------------------------------------- *)

let ETA_AX = new_axiom
  `!t:A->B. (\x. t x) = t`;;

let ETA_CONV =
  let t = `t:A->B` in
  let pth = prove(`(\x. (t:A->B) x) = t`,MATCH_ACCEPT_TAC ETA_AX) in
  fun tm ->
    try let bv,bod = dest_abs tm in
        let l,r = dest_comb bod in
        if r = bv && not (vfree_in bv l) then
          TRANS (REFL tm) (PINST [type_of bv,aty; type_of bod,bty] [l,t] pth)
        else fail()
    with Failure _ -> failwith "ETA_CONV";;

let EQ_EXT = prove
 (`!(f:A->B) g. (!x. f x = g x) ==> f = g`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o ABS `x:A` o SPEC `x:A`) THEN
  REWRITE_TAC[ETA_AX]);;

let FUN_EQ_THM = prove
 (`!(f:A->B) g. f = g <=> (!x. f x = g x)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN GEN_TAC THEN REFL_TAC;
    MATCH_ACCEPT_TAC EQ_EXT]);;

(* ------------------------------------------------------------------------- *)
(* Indefinite descriptor (giving AC).                                        *)
(* ------------------------------------------------------------------------- *)

new_constant("@",`:(A->bool)->A`);;

parse_as_binder "@";;

let is_select = is_binder "@";;
let dest_select = dest_binder "@";;
let mk_select = mk_binder "@";;

let SELECT_AX = new_axiom
 `!P (x:A). P x ==> P((@) P)`;;

(* ------------------------------------------------------------------------- *)
(* Useful for compatibility. (The old EXISTS_DEF.)                           *)
(* ------------------------------------------------------------------------- *)

let EXISTS_THM = prove
 (`(?) = \P:A->bool. P ((@) P)`,
  MATCH_MP_TAC EQ_EXT THEN BETA_TAC THEN X_GEN_TAC `P:A->bool` THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
  EQ_TAC THENL
   [DISCH_THEN(CHOOSE_THEN MP_TAC) THEN MATCH_ACCEPT_TAC SELECT_AX;
    DISCH_TAC THEN EXISTS_TAC `((@) P):A` THEN POP_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Rules and so on for the select operator.                                  *)
(* ------------------------------------------------------------------------- *)

let SELECT_RULE =
  let P = `P:A->bool` in
  let pth = prove
   (`(?) (P:A->bool) ==> P((@) P)`,
    SIMP_TAC[SELECT_AX; ETA_AX]) in
  fun th ->
    try let abs = rand(concl th) in
        let ty = type_of(bndvar abs) in
        CONV_RULE BETA_CONV (MP (PINST [ty,aty] [abs,P] pth) th)
    with Failure _ -> failwith "SELECT_RULE";;

let SELECT_CONV =
  let P = `P:A->bool` in
  let pth = prove
   (`(P:A->bool)((@) P) = (?) P`,
    REWRITE_TAC[EXISTS_THM] THEN BETA_TAC THEN REFL_TAC) in
   fun tm ->
     try let is_epsok t = is_select t &&
                          let bv,bod = dest_select t in
                          aconv tm (vsubst [t,bv] bod) in
         let pickeps = find_term is_epsok tm in
         let abs = rand pickeps in
         let ty = type_of (bndvar abs) in
         CONV_RULE (LAND_CONV BETA_CONV) (PINST [ty,aty] [abs,P] pth)
     with Failure _ -> failwith "SELECT_CONV";;

(* ------------------------------------------------------------------------- *)
(* Some basic theorems.                                                      *)
(* ------------------------------------------------------------------------- *)

let SELECT_REFL = prove
 (`!x:A. (@y. y = x) = x`,
  GEN_TAC THEN CONV_TAC SELECT_CONV THEN
  EXISTS_TAC `x:A` THEN REFL_TAC);;

let SELECT_UNIQUE = prove
 (`!P x. (!y:A. P y = (y = x)) ==> ((@) P = x)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
  ASM_REWRITE_TAC[SELECT_REFL]);;

extend_basic_rewrites [SELECT_REFL];;

(* ------------------------------------------------------------------------- *)
(* Now we can derive type definitions from existence; check benignity.       *)
(* ------------------------------------------------------------------------- *)

let the_type_definitions = ref ([]:((string*string*string)*(thm*thm))list);;

let new_type_definition tyname (absname,repname) th =
  try let th',tth' = assoc (tyname,absname,repname) (!the_type_definitions) in
      if concl th' <> concl th then failwith "" else
      (warn true "Benign redefinition of type"; tth')
  with Failure _ ->
    let th0 =
     CONV_RULE (RATOR_CONV (REWR_CONV EXISTS_THM) THENC BETA_CONV) th in
    let th1,th2 = new_basic_type_definition tyname (absname,repname) th0 in
    let tth = CONJ (GEN_ALL th1)
                   (GEN_ALL (CONV_RULE(LAND_CONV (TRY_CONV BETA_CONV)) th2)) in
    the_type_definitions := ((tyname,absname,repname),(th,tth))::
                            (!the_type_definitions);
    tth;;

(* ------------------------------------------------------------------------- *)
(* Derive excluded middle. The proof is an optimization due to Mark Adams of *)
(* the original Diaconescu proof as presented in Beeson's book.              *)
(* ------------------------------------------------------------------------- *)

let EXCLUDED_MIDDLE = prove
 (`!t. t \/ ~t`,
  GEN_TAC THEN SUBGOAL_THEN
   `(((@x. (x <=> F) \/ t) <=> F) \/ t) /\ (((@x. (x <=> T) \/ t) <=> T) \/ t)`
  MP_TAC THENL
   [CONJ_TAC THEN CONV_TAC SELECT_CONV THENL
     [EXISTS_TAC `F`; EXISTS_TAC `T`] THEN
    DISJ1_TAC THEN REFL_TAC;
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    TRY(DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC) THEN
    DISJ2_TAC THEN DISCH_TAC THEN MP_TAC(ITAUT `~(T <=> F)`) THEN
    PURE_ONCE_ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[ITAUT `p \/ T <=> T`]]);;

let BOOL_CASES_AX = prove
 (`!t. (t <=> T) \/ (t <=> F)`,
  GEN_TAC THEN DISJ_CASES_TAC(SPEC `t:bool` EXCLUDED_MIDDLE) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Classically based tactics. (See also COND_CASES_TAC later on.)            *)
(* ------------------------------------------------------------------------- *)

let BOOL_CASES_TAC p = STRUCT_CASES_TAC (SPEC p BOOL_CASES_AX);;

let ASM_CASES_TAC t = DISJ_CASES_TAC(SPEC t EXCLUDED_MIDDLE);;

(* ------------------------------------------------------------------------- *)
(* Set up a reasonable tautology checker for classical logic.                *)
(* ------------------------------------------------------------------------- *)

let TAUT =
  let PROP_REWRITE_TAC = REWRITE_TAC[] in
  let RTAUT_TAC (asl,w) =
    let ok t = type_of t = bool_ty && can (find_term is_var) t && free_in t w in
    (PROP_REWRITE_TAC THEN
     W((fun t1 t2 -> t1 THEN t2) (REWRITE_TAC[]) o BOOL_CASES_TAC o
       hd o sort free_in o find_terms ok o snd)) (asl,w) in
  let TAUT_TAC = REPEAT(GEN_TAC ORELSE CONJ_TAC) THEN REPEAT RTAUT_TAC in
  fun tm -> prove(tm,TAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* A few useful classical tautologies.                                       *)
(* ------------------------------------------------------------------------- *)

let DE_MORGAN_THM = TAUT
  `!t1 t2. (~(t1 /\ t2) <=> ~t1 \/ ~t2) /\ (~(t1 \/ t2) <=> ~t1 /\ ~t2)`;;

let NOT_CLAUSES =
  TAUT `(!t. ~ ~t <=> t) /\ (~T <=> F) /\ (~F <=> T)`;;

let NOT_IMP = TAUT `!t1 t2. ~(t1 ==> t2) <=> t1 /\ ~t2`;;

let CONTRAPOS_THM = TAUT `!t1 t2. (~t1 ==> ~t2) <=> (t2 ==> t1)`;;

extend_basic_rewrites [CONJUNCT1 NOT_CLAUSES];;

(* ------------------------------------------------------------------------- *)
(* Some classically based rules.                                             *)
(* ------------------------------------------------------------------------- *)

let CCONTR =
  let P = `P:bool` in
  let pth = TAUT `(~P ==> F) ==> P` in
  fun tm th ->
    try let tm' = mk_neg tm in
        MP (INST [tm,P] pth) (DISCH tm' th)
    with Failure _ -> failwith "CCONTR";;

let CONTRAPOS_CONV =
  let a = `a:bool` and b = `b:bool` in
  let pth = TAUT `(a ==> b) <=> (~b ==> ~a)` in
  fun tm ->
    try let P,Q = dest_imp tm in
        INST [P,a; Q,b] pth
    with Failure _ -> failwith "CONTRAPOS_CONV";;

(* ------------------------------------------------------------------------- *)
(* A classicalal "refutation" tactic.                                        *)
(* ------------------------------------------------------------------------- *)

let REFUTE_THEN =
  let f_tm = `F`
  and conv = REWR_CONV(TAUT `p <=> ~p ==> F`) in
  fun ttac (asl,w as gl) ->
    if w = f_tm then ALL_TAC gl
    else if is_neg w then DISCH_THEN ttac gl
    else (CONV_TAC conv THEN DISCH_THEN ttac) gl;;

(* ------------------------------------------------------------------------- *)
(* Infinite de Morgan laws.                                                  *)
(* ------------------------------------------------------------------------- *)

let NOT_EXISTS_THM = prove
 (`!P. ~(?x:A. P x) <=> (!x. ~(P x))`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN UNDISCH_TAC `~(?x:A. P x)` THEN
    REWRITE_TAC[] THEN EXISTS_TAC `x:A` THEN POP_ASSUM ACCEPT_TAC;
    DISCH_THEN(CHOOSE_THEN MP_TAC) THEN ASM_REWRITE_TAC[]]);;

let EXISTS_NOT_THM = prove
 (`!P. (?x:A. ~(P x)) <=> ~(!x. P x)`,
  ONCE_REWRITE_TAC[TAUT `(a <=> ~b) <=> (~a <=> b)`] THEN
  REWRITE_TAC[NOT_EXISTS_THM]);;

let NOT_FORALL_THM = prove
 (`!P. ~(!x. P x) <=> (?x:A. ~(P x))`,
  MATCH_ACCEPT_TAC(GSYM EXISTS_NOT_THM));;

let FORALL_NOT_THM = prove
 (`!P. (!x. ~(P x)) <=> ~(?x:A. P x)`,
  MATCH_ACCEPT_TAC(GSYM NOT_EXISTS_THM));;

(* ------------------------------------------------------------------------- *)
(* Expand quantification over Booleans.                                      *)
(* ------------------------------------------------------------------------- *)

let FORALL_BOOL_THM = prove
  (`(!b. P b) <=> P T /\ P F`,
   EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
   GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[]);;

let EXISTS_BOOL_THM = prove
 (`(?b. P b) <=> P T \/ P F`,
  MATCH_MP_TAC(TAUT `(~p <=> ~q) ==> (p <=> q)`) THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM; FORALL_BOOL_THM]);;

(* ------------------------------------------------------------------------- *)
(* Universal quantifier and disjunction                                      *)
(* ------------------------------------------------------------------------- *)

let LEFT_FORALL_OR_THM = prove
 (`!P Q. (!x:A. P x \/ Q) <=> (!x. P x) \/ Q`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `(a <=> b) <=> (~a <=> ~b)`] THEN
  REWRITE_TAC[NOT_FORALL_THM; DE_MORGAN_THM; LEFT_EXISTS_AND_THM]);;

let RIGHT_FORALL_OR_THM = prove
 (`!P Q. (!x:A. P \/ Q x) <=> P \/ (!x. Q x)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `(a <=> b) <=> (~a <=> ~b)`] THEN
  REWRITE_TAC[NOT_FORALL_THM; DE_MORGAN_THM; RIGHT_EXISTS_AND_THM]);;

let LEFT_OR_FORALL_THM = prove
 (`!P Q. (!x:A. P x) \/ Q <=> (!x. P x \/ Q)`,
  MATCH_ACCEPT_TAC(GSYM LEFT_FORALL_OR_THM));;

let RIGHT_OR_FORALL_THM = prove
 (`!P Q. P \/ (!x:A. Q x) <=> (!x. P \/ Q x)`,
  MATCH_ACCEPT_TAC(GSYM RIGHT_FORALL_OR_THM));;

(* ------------------------------------------------------------------------- *)
(* Implication and quantifiers.                                              *)
(* ------------------------------------------------------------------------- *)

let LEFT_IMP_FORALL_THM = prove
 (`!P Q. ((!x:A. P x) ==> Q) <=> (?x. P x ==> Q)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `(a <=> b) <=> (~a <=> ~b)`] THEN
  REWRITE_TAC[NOT_EXISTS_THM; NOT_IMP; LEFT_AND_FORALL_THM]);;

let LEFT_EXISTS_IMP_THM = prove
 (`!P Q. (?x. P x ==> Q) <=> ((!x:A. P x) ==> Q)`,
  MATCH_ACCEPT_TAC(GSYM LEFT_IMP_FORALL_THM));;

let RIGHT_IMP_EXISTS_THM = prove
 (`!P Q. (P ==> ?x:A. Q x) <=> (?x:A. P ==> Q x)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `(a <=> b) <=> (~a <=> ~b)`] THEN
  REWRITE_TAC[NOT_EXISTS_THM; NOT_IMP; RIGHT_AND_FORALL_THM]);;

let RIGHT_EXISTS_IMP_THM = prove
 (`!P Q. (?x:A. P ==> Q x) <=> (P ==> ?x:A. Q x)`,
  MATCH_ACCEPT_TAC(GSYM RIGHT_IMP_EXISTS_THM));;

(* ------------------------------------------------------------------------- *)
(* The conditional.                                                          *)
(* ------------------------------------------------------------------------- *)

let COND_DEF = new_definition
  `COND = \t t1 t2. @x:A. ((t <=> T) ==> (x = t1)) /\
                          ((t <=> F) ==> (x = t2))`;;

let COND_CLAUSES = prove
 (`!(t1:A) t2. ((if T then t1 else t2) = t1) /\
               ((if F then t1 else t2) = t2)`,
  REWRITE_TAC[COND_DEF]);;

let is_cond tm =
  try fst(dest_const(rator(rator (rator tm)))) = "COND"
  with Failure _ -> false;;

let mk_cond (b,x,y) =
  try let c = mk_const("COND",[type_of x,aty]) in
      mk_comb(mk_comb(mk_comb(c,b),x),y)
  with Failure _ -> failwith "mk_cond";;

let dest_cond tm =
  try let tm1,y = dest_comb tm in
      let tm2,x = dest_comb tm1 in
      let c,b = dest_comb tm2 in
      if fst(dest_const c) = "COND" then (b,(x,y)) else fail()
  with Failure _ -> failwith "dest_cond";;

extend_basic_rewrites [COND_CLAUSES];;

let COND_EXPAND = prove
 (`!b t1 t2. (if b then t1 else t2) <=> (~b \/ t1) /\ (b \/ t2)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[]);;

let COND_ID = prove
 (`!b (t:A). (if b then t else t) = t`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;

let COND_RAND = prove
 (`!b (f:A->B) x y. f (if b then x else y) = (if b then f x else f y)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;

let COND_RATOR = prove
 (`!b (f:A->B) g x. (if b then f else g)(x) = (if b then f x else g x)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;

let COND_ABS = prove
 (`!b (f:A->B) g. (\x. if b then f x else g x) = (if b then f else g)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[ETA_AX]);;

let COND_SWAP = prove
 (`!p x y:A. (if ~p then x else y) = (if p then y else x)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `p:bool` THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Redefine TAUT to freeze in the rewrites including COND.                   *)
(* ------------------------------------------------------------------------- *)

let TAUT =
  let PROP_REWRITE_TAC = REWRITE_TAC[] in
  let RTAUT_TAC (asl,w) =
    let ok t = type_of t = bool_ty && can (find_term is_var) t && free_in t w in
    (PROP_REWRITE_TAC THEN
     W((fun t1 t2 -> t1 THEN t2) (REWRITE_TAC[]) o BOOL_CASES_TAC o
       hd o sort free_in o find_terms ok o snd)) (asl,w) in
  let TAUT_TAC = REPEAT(GEN_TAC ORELSE CONJ_TAC) THEN REPEAT RTAUT_TAC in
  fun tm ->
    try prove(tm,TAUT_TAC)
    with Failure _ ->
      failwith ("TAUT `" ^ (string_of_term tm) ^ "`: cannot solve");;

(* ------------------------------------------------------------------------- *)
(* Throw monotonicity in.                                                    *)
(* ------------------------------------------------------------------------- *)

let MONO_COND = prove
 (`(A ==> B) /\ (C ==> D) ==> (if b then A else C) ==> (if b then B else D)`,
  STRIP_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[]);;

monotonicity_theorems := MONO_COND::(!monotonicity_theorems);;

(* ------------------------------------------------------------------------- *)
(* Tactic for splitting over an arbitrarily chosen conditional.              *)
(* ------------------------------------------------------------------------- *)

let COND_ELIM_THM = prove
 (`(P:A->bool) (if c then x else y) <=> (c ==> P x) /\ (~c ==> P y)`,
  BOOL_CASES_TAC `c:bool` THEN REWRITE_TAC[]);;

let COND_ELIM_CONV = HIGHER_REWRITE_CONV[COND_ELIM_THM] true;;

let (COND_CASES_TAC :tactic) =
  let DENEG_RULE = GEN_REWRITE_RULE I [TAUT `~ ~ p <=> p`] in
  CONV_TAC COND_ELIM_CONV THEN CONJ_TAC THENL
    [DISCH_THEN(fun th -> ASSUME_TAC th THEN SUBST1_TAC(EQT_INTRO th));
     DISCH_THEN(fun th -> try let th' = DENEG_RULE th in
                              ASSUME_TAC th' THEN SUBST1_TAC(EQT_INTRO th')
                          with Failure _ ->
                              ASSUME_TAC th THEN SUBST1_TAC(EQF_INTRO th))];;

(* ------------------------------------------------------------------------- *)
(* Skolemization.                                                            *)
(* ------------------------------------------------------------------------- *)

let SKOLEM_THM = prove
 (`!P. (!x:A. ?y:B. P x y) <=> (?y. !x. P x (y x))`,
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THENL
   [EXISTS_TAC `\x:A. @y:B. P x y` THEN GEN_TAC THEN
    BETA_TAC THEN CONV_TAC SELECT_CONV;
    EXISTS_TAC `(y:A->B) x`] THEN
  POP_ASSUM MATCH_ACCEPT_TAC);;

let SKOLEM_THM_GEN = prove
 (`!P R. (!x:A. P x ==> ?y:B. R x y) <=> (?f. !x. P x ==> R x (f x))`,
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]);;

(* ------------------------------------------------------------------------- *)
(* NB: this one is true intutionistically and intensionally.                 *)
(* ------------------------------------------------------------------------- *)

let UNIQUE_SKOLEM_ALT = prove
 (`!P:A->B->bool. (!x. ?!y. P x y) <=> ?f. !x y. P x y <=> (f x = y)`,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_ALT; SKOLEM_THM]);;

(* ------------------------------------------------------------------------- *)
(* and this one intuitionistically and extensionally.                        *)
(* ------------------------------------------------------------------------- *)

let UNIQUE_SKOLEM_THM = prove
 (`!P. (!x:A. ?!y:B. P x y) <=> (?!f. !x. P x (f x))`,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM; SKOLEM_THM; FORALL_AND_THM] THEN
  EQ_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THENL
   [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `x:A` THEN FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`x:A`; `y1:B`; `y2:B`] THEN STRIP_TAC THEN
    FIRST_ASSUM(X_CHOOSE_TAC `f:A->B`) THEN
    SUBGOAL_THEN `(\z. if z = x then y1 else (f:A->B) z) =
                  (\z. if z = x then y2 else (f:A->B) z)` MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN
      REPEAT STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o C AP_THM `x:A`) THEN REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Extend default congruences for contextual rewriting.                      *)
(* ------------------------------------------------------------------------- *)

let COND_CONG =
  TAUT `(g = g') ==>
        (g' ==> (t = t')) ==>
        (~g' ==> (e = e')) ==>
        ((if g then t else e) = (if g' then t' else e'))` in
  extend_basic_congs [COND_CONG];;

let COND_EQ_CLAUSE = prove
 (`(if x = x then y else z) = y`,
  REWRITE_TAC[]) in
 extend_basic_rewrites [COND_EQ_CLAUSE];;

(* ------------------------------------------------------------------------- *)
(* We can now treat "bool" as an enumerated type for some purposes.          *)
(* ------------------------------------------------------------------------- *)

let bool_INDUCT = prove
 (`!P. P F /\ P T ==> !x. P x`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(SPEC `x:bool` BOOL_CASES_AX) THEN
  ASM_REWRITE_TAC[]);;

let bool_RECURSION = prove
 (`!a b:A. ?f. f F = a /\ f T = b`,
  REPEAT GEN_TAC THEN EXISTS_TAC `\x. if x then b:A else a` THEN
  REWRITE_TAC[]);;

let inductive_type_store = ref
 ["bool",(2,bool_INDUCT,bool_RECURSION)];;
