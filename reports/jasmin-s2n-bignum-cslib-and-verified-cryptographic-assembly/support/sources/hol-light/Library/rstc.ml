(* ========================================================================= *)
(* All you wanted to know about reflexive symmetric and transitive closures. *)
(* ========================================================================= *)

prioritize_num();;

let RULE_INDUCT_TAC =
  MATCH_MP_TAC o DISCH_ALL o SPEC_ALL o UNDISCH o SPEC_ALL;;

(* ------------------------------------------------------------------------- *)
(* Little lemmas about equivalent forms of symmetry and transitivity.        *)
(* ------------------------------------------------------------------------- *)

let SYM_ALT = prove
 (`!R:A->A->bool. (!x y. R x y ==> R y x) <=> (!x y. R x y <=> R y x)`,
  GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [EQ_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC;
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [th])] THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);;

let TRANS_ALT = prove
 (`!(R:A->A->bool) (S:A->A->bool) U.
        (!x z. (?y. R x y /\ S y z) ==> U x z) <=>
        (!x y z. R x y /\ S y z ==> U x z)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Reflexive closure                                                         *)
(* ------------------------------------------------------------------------- *)

let RC_RULES,RC_INDUCT,RC_CASES = new_inductive_definition
  `(!x y. R x y ==> RC R x y) /\
   (!x:A. RC R x x)`;;

let RC_INC = prove
 (`!(R:A->A->bool) x y. R x y ==> RC R x y`,
  REWRITE_TAC[RC_RULES]);;

let RC_REFL = prove
 (`!(R:A->A->bool) x. RC R x x`,
  REWRITE_TAC[RC_RULES]);;

let RC_EXPLICIT = prove
 (`!(R:A->A->bool) x y. RC R x y <=> R x y \/ (x = y)`,
  REWRITE_TAC[RC_CASES; EQ_SYM_EQ]);;

let RC_MONO = prove
 (`!(R:A->A->bool) S.
        (!x y. R x y ==> S x y) ==>
            (!x y. RC R x y ==> RC S x y)`,
  MESON_TAC[RC_CASES]);;

let RC_CLOSED = prove
 (`!R:A->A->bool. (RC R = R) <=> !x. R x x`,
  REWRITE_TAC[FUN_EQ_THM; RC_EXPLICIT] THEN MESON_TAC[]);;

let RC_IDEMP = prove
 (`!R:A->A->bool. RC(RC R) = RC R`,
  REWRITE_TAC[RC_CLOSED; RC_REFL]);;

let RC_SYM = prove
 (`!R:A->A->bool.
        (!x y. R x y ==> R y x) ==> (!x y. RC R x y ==> RC R y x)`,
  MESON_TAC[RC_CASES]);;

let RC_TRANS = prove
 (`!R:A->A->bool.
        (!x y z. R x y /\ R y z ==> R x z) ==>
        (!x y z. RC R x y /\ RC R y z ==> RC R x z)`,
  REWRITE_TAC[RC_CASES] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Symmetric closure                                                         *)
(* ------------------------------------------------------------------------- *)

let SC_RULES,SC_INDUCT,SC_CASES = new_inductive_definition
  `(!x y. R x y ==> SC R x y) /\
   (!x:A y. SC R x y ==> SC R y x)`;;

let SC_INC = prove
 (`!(R:A->A->bool) x y. R x y ==> SC R x y`,
  REWRITE_TAC[SC_RULES]);;

let SC_SYM = prove
 (`!(R:A->A->bool) x y. SC R x y ==> SC R y x`,
  REWRITE_TAC[SC_RULES]);;

let SC_EXPLICIT = prove
 (`!R:A->A->bool. SC(R) x y <=> R x y \/ R y x`,
  GEN_TAC THEN EQ_TAC THENL
   [RULE_INDUCT_TAC SC_INDUCT THEN MESON_TAC[]; MESON_TAC[SC_CASES]]);;

let SC_MONO = prove
 (`!(R:A->A->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. SC R x y ==> SC S x y)`,
  MESON_TAC[SC_EXPLICIT]);;

let SC_CLOSED = prove
 (`!R:A->A->bool. (SC R = R) <=> !x y. R x y ==> R y x`,
  REWRITE_TAC[FUN_EQ_THM; SC_EXPLICIT] THEN MESON_TAC[]);;

let SC_IDEMP = prove
 (`!R:A->A->bool. SC(SC R) = SC R`,
  REWRITE_TAC[SC_CLOSED; SC_SYM]);;

let SC_REFL = prove
 (`!R:A->A->bool. (!x. R x x) ==> (!x. SC R x x)`,
  MESON_TAC[SC_EXPLICIT]);;

(* ------------------------------------------------------------------------- *)
(* Transitive closure                                                        *)
(* ------------------------------------------------------------------------- *)

let TC_RULES,TC_INDUCT,TC_CASES = new_inductive_definition
   `(!x y. R x y ==> TC R x y) /\
    (!(x:A) y z. TC R x y /\ TC R y z ==> TC R x z)`;;

let TC_INC = prove
 (`!(R:A->A->bool) x y. R x y ==> TC R x y`,
  REWRITE_TAC[TC_RULES]);;

let TC_TRANS = prove
 (`!(R:A->A->bool) x y z. TC R x y /\ TC R y z ==> TC R x z`,
  REWRITE_TAC[TC_RULES]);;

let TC_MONO = prove
 (`!(R:A->A->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. TC R x y ==> TC S x y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC TC_INDUCT THEN ASM_MESON_TAC[TC_RULES]);;

let TC_CLOSED = prove
 (`!R:A->A->bool. (TC R = R) <=> !x y z. R x y /\ R y z ==> R x z`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN EQ_TAC THENL
   [MESON_TAC[TC_RULES]; REPEAT STRIP_TAC] THEN
  EQ_TAC THENL
   [RULE_INDUCT_TAC TC_INDUCT THEN ASM_MESON_TAC[];
    MESON_TAC[TC_RULES]]);;

let TC_IDEMP = prove
 (`!R:A->A->bool. TC(TC R) = TC R`,
  REWRITE_TAC[TC_CLOSED; TC_TRANS]);;

let TC_REFL = prove
 (`!R:A->A->bool. (!x. R x x) ==> (!x. TC R x x)`,
  MESON_TAC[TC_INC]);;

let TC_SYM = prove
 (`!R:A->A->bool. (!x y. R x y ==> R y x) ==> (!x y. TC R x y ==> TC R y x)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC TC_INDUCT THEN
  ASM_MESON_TAC[TC_RULES]);;

(* ------------------------------------------------------------------------- *)
(* Commutativity properties of the three basic closure operations            *)
(* ------------------------------------------------------------------------- *)

let RC_SC = prove
 (`!R:A->A->bool. RC(SC R) = SC(RC R)`,
  REWRITE_TAC[FUN_EQ_THM; RC_EXPLICIT; SC_EXPLICIT] THEN MESON_TAC[]);;

let SC_RC = prove
 (`!R:A->A->bool. SC(RC R) = RC(SC R)`,
  REWRITE_TAC[RC_SC]);;

let RC_TC = prove
 (`!R:A->A->bool. RC(TC R) = TC(RC R)`,
  REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN EQ_TAC THENL
   [RULE_INDUCT_TAC RC_INDUCT THEN MESON_TAC[TC_RULES; RC_RULES; TC_MONO];
    RULE_INDUCT_TAC TC_INDUCT THEN MESON_TAC[RC_TRANS; TC_RULES; RC_MONO]]);;

let TC_RC = prove
 (`!R:A->A->bool. TC(RC R) = RC(TC R)`,
  REWRITE_TAC[RC_TC]);;

let TC_SC = prove
 (`!(R:A->A->bool) x y. SC(TC R) x y ==> TC(SC R) x y`,
  GEN_TAC THEN MATCH_MP_TAC SC_INDUCT THEN
  MESON_TAC[TC_MONO; TC_SYM; SC_RULES]);;

let SC_TC = prove
 (`!(R:A->A->bool) x y. SC(TC R) x y ==> TC(SC R) x y`,
  REWRITE_TAC[TC_SC]);;

(* ------------------------------------------------------------------------- *)
(* Left and right variants of TC.                                            *)
(* ------------------------------------------------------------------------- *)

let TC_TRANS_L = prove
 (`!(R:A->A->bool) x y z. TC R x y /\ R y z ==> TC R x z`,
  MESON_TAC[TC_RULES]);;

let TC_TRANS_R = prove
 (`!(R:A->A->bool) x y z. R x y /\ TC R y z ==> TC R x z`,
  MESON_TAC[TC_RULES]);;

let TC_CASES_L = prove
 (`!(R:A->A->bool) x z. TC R x z <=> R x z \/ (?y. TC R x y /\ R y z)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [RULE_INDUCT_TAC TC_INDUCT THEN MESON_TAC[TC_RULES]; MESON_TAC[TC_RULES]]);;

let TC_CASES_R = prove
 (`!(R:A->A->bool) x z. TC R x z <=> R x z \/ (?y. R x y /\ TC R y z)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [RULE_INDUCT_TAC TC_INDUCT THEN MESON_TAC[TC_RULES]; MESON_TAC[TC_RULES]]);;

let TC_INDUCT_L = prove
 (`!(R:A->A->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x y z. P x y /\ R y z ==> P x z) ==>
            (!x y. TC R x y ==> P x y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:A z. TC(R) y z ==> !x:A. P x y ==> P x z` MP_TAC THENL
   [MATCH_MP_TAC TC_INDUCT THEN ASM_MESON_TAC[]; ASM_MESON_TAC[TC_CASES_R]]);;

let TC_INDUCT_R = prove
 (`!(R:A->A->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x z. (?y. R x y /\ P y z) ==> P x z) ==>
            (!x y. TC R x y ==> P x y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:A y. TC(R) x y ==> !z:A. P y z ==> P x z` MP_TAC THENL
   [MATCH_MP_TAC TC_INDUCT THEN ASM_MESON_TAC[]; ASM_MESON_TAC[TC_CASES_L]]);;

let WF_TC = prove
 (`!R:A->A->bool. WF(TC R) <=> WF(R)`,
  GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[WF_SUBSET; TC_INC];
    REWRITE_TAC[WF] THEN DISCH_TAC THEN X_GEN_TAC `P:A->bool` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\y:A. ?z. P z /\ TC(R) z y`) THEN
    REWRITE_TAC[] THEN MESON_TAC[TC_CASES_L]]);;

(* ------------------------------------------------------------------------- *)
(* Reflexive symmetric closure                                               *)
(* ------------------------------------------------------------------------- *)

let RSC = new_definition
  `RSC(R:A->A->bool) = RC(SC R)`;;

let RSC_INC = prove
 (`!(R:A->A->bool) x y. R x y ==> RSC R x y`,
  REWRITE_TAC[RSC] THEN MESON_TAC[RC_INC; SC_INC]);;

let RSC_REFL = prove
 (`!(R:A->A->bool) x. RSC R x x`,
  REWRITE_TAC[RSC; RC_REFL]);;

let RSC_SYM = prove
 (`!(R:A->A->bool) x y. RSC R x y ==> RSC R y x`,
  REWRITE_TAC[RSC; RC_SC; SC_SYM]);;

let RSC_CASES = prove
 (`!(R:A->A->bool) x y. RSC R x y <=> (x = y) \/ R x y \/ R y x`,
  REWRITE_TAC[RSC; RC_EXPLICIT; SC_EXPLICIT; DISJ_ACI]);;

let RSC_INDUCT = prove
 (`!(R:A->A->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x. P x x) /\
        (!x y. P x y ==> P y x)
        ==>  !x y. RSC R x y ==> P x y`,
  REWRITE_TAC[RSC; RC_EXPLICIT; SC_EXPLICIT] THEN MESON_TAC[]);;

let RSC_MONO = prove
 (`!(R:A->A->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. RSC R x y ==> RSC S x y)`,
  REWRITE_TAC[RSC] THEN MESON_TAC[SC_MONO; RC_MONO]);;

let RSC_CLOSED = prove
 (`!R:A->A->bool. (RSC R = R) <=> (!x. R x x) /\ (!x y. R x y ==> R y x)`,
  REWRITE_TAC[FUN_EQ_THM; RSC; RC_EXPLICIT; SC_EXPLICIT] THEN MESON_TAC[]);;

let RSC_IDEMP = prove
 (`!R:A->A->bool. RSC(RSC R) = RSC R`,
  REWRITE_TAC[RSC_CLOSED; RSC_REFL; RSC_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Reflexive transitive closure                                              *)
(* ------------------------------------------------------------------------- *)

let RTC = new_definition
  `RTC(R:A->A->bool) = RC(TC R)`;;

let RTC_INC = prove
 (`!(R:A->A->bool) x y. R x y ==> RTC R x y`,
  REWRITE_TAC[RTC] THEN MESON_TAC[RC_INC; TC_INC]);;

let RTC_REFL = prove
 (`!(R:A->A->bool) x. RTC R x x`,
  REWRITE_TAC[RTC; RC_REFL]);;

let RTC_TRANS = prove
 (`!(R:A->A->bool) x y z. RTC R x y /\ RTC R y z ==> RTC R x z`,
  REWRITE_TAC[RTC; RC_TC; TC_TRANS]);;

let RTC_RULES = prove
 (`!(R:A->A->bool).
        (!x y. R x y ==> RTC R x y) /\
        (!x. RTC R x x) /\
        (!x y z. RTC R x y /\ RTC R y z ==> RTC R x z)`,
  REWRITE_TAC[RTC_INC; RTC_REFL; RTC_TRANS]);;

let RTC_TRANS_L = prove
 (`!(R:A->A->bool) x y z. RTC R x y /\ R y z ==> RTC R x z`,
  REWRITE_TAC[RTC; RC_TC] THEN MESON_TAC[TC_TRANS_L; RC_INC]);;

let RTC_TRANS_R = prove
 (`!(R:A->A->bool) x y z. R x y /\ RTC R y z ==> RTC R x z`,
  REWRITE_TAC[RTC; RC_TC] THEN MESON_TAC[TC_TRANS_R; RC_INC]);;

let RTC_CASES = prove
 (`!(R:A->A->bool) x z. RTC R x z <=> (x = z) \/ ?y. RTC R x y /\ RTC R y z`,
  REWRITE_TAC[RTC; RC_EXPLICIT] THEN MESON_TAC[TC_TRANS]);;

let RTC_CASES_L = prove
 (`!(R:A->A->bool) x z. RTC R x z <=> (x = z) \/ ?y. RTC R x y /\ R y z`,
  REWRITE_TAC[RTC; RC_EXPLICIT] THEN MESON_TAC[TC_CASES_L; TC_TRANS_L]);;

let RTC_CASES_R = prove
 (`!(R:A->A->bool) x z. RTC R x z <=> (x = z) \/ ?y. R x y /\ RTC R y z`,
  REWRITE_TAC[RTC; RC_EXPLICIT] THEN MESON_TAC[TC_CASES_R; TC_TRANS_R]);;

let RTC_INDUCT = prove
 (`!(R:A->A->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x. P x x) /\
        (!x y z. P x y /\ P y z ==> P x z)
        ==> !x y. RTC R x y ==> P x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[RTC; RC_TC] THEN
  MATCH_MP_TAC TC_INDUCT THEN REWRITE_TAC[RC_EXPLICIT] THEN ASM_MESON_TAC[]);;

let RTC_INDUCT_L = prove
 (`!(R:A->A->bool) P.
        (!x. P x x) /\
        (!x y z. P x y /\ R y z ==> P x z)
        ==> !x y. RTC R x y ==> P x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[RTC; RC_TC] THEN
  MATCH_MP_TAC TC_INDUCT_L THEN REWRITE_TAC[RC_EXPLICIT] THEN
  ASM_MESON_TAC[]);;

let RTC_INDUCT_R = prove
 (`!(R:A->A->bool) P.
        (!x. P x x) /\
        (!x y z. R x y /\ P y z ==> P x z)
        ==> !x y. RTC R x y ==> P x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[RTC; RC_TC] THEN
  MATCH_MP_TAC TC_INDUCT_R THEN REWRITE_TAC[RC_EXPLICIT] THEN
  ASM_MESON_TAC[]);;

let RTC_MONO = prove
 (`!(R:A->A->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. RTC R x y ==> RTC S x y)`,
  REWRITE_TAC[RTC] THEN MESON_TAC[RC_MONO; TC_MONO]);;

let RTC_CLOSED = prove
 (`!R:A->A->bool. (RTC R = R) <=> (!x. R x x) /\
                                  (!x y z. R x y /\ R y z ==> R x z)`,
  REWRITE_TAC[FUN_EQ_THM; RTC; RC_EXPLICIT] THEN
  MESON_TAC[TC_CLOSED; TC_RULES]);;

let RTC_IDEMP = prove
 (`!R:A->A->bool. RTC(RTC R) = RTC R`,
  REWRITE_TAC[RTC_CLOSED; RTC_REFL; RTC_TRANS]);;

let RTC_SYM = prove
 (`!R:A->A->bool. (!x y. R x y ==> R y x) ==> (!x y. RTC R x y ==> RTC R y x)`,
  REWRITE_TAC[RTC] THEN MESON_TAC[RC_SYM; TC_SYM]);;

let RTC_STUTTER = prove
 (`RTC R = RTC (\x y. R x y /\ ~(x = y))`,
  REWRITE_TAC[RC_TC; RTC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  REWRITE_TAC[RC_CASES] THEN MESON_TAC[]);;

let TC_RTC_CASES_L = prove
 (`TC R x z <=> ?y. RTC R x y /\ R y z`,
  REWRITE_TAC[RTC; RC_CASES] THEN MESON_TAC[TC_CASES_L; TC_INC]);;

let TC_RTC_CASES_R = prove
 (`!R x z. TC R x z <=> ?y. R x y /\ RTC R y z`,
  REWRITE_TAC[RTC; RC_CASES] THEN MESON_TAC[TC_CASES_R; TC_INC]);;

let TC_TC_RTC_CASES = prove
 (`!R x z. TC R x z <=> ?y. TC R x y /\ RTC R y z`,
  REWRITE_TAC[RTC; RC_CASES] THEN MESON_TAC[TC_TRANS]);;

let TC_RTC_TC_CASES = prove
 (`!R x z. TC R x z <=> ?y. RTC R x y /\ TC R y z`,
  REWRITE_TAC[RTC; RC_CASES] THEN MESON_TAC[TC_TRANS]);;

let RTC_NE_IMP_TC = prove
 (`!R x y. RTC R x y /\ ~(x = y) ==> TC R x y`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM IMP_IMP] THEN
  MATCH_MP_TAC RTC_INDUCT THEN REWRITE_TAC[] THEN
  MESON_TAC[TC_INC; TC_CASES]);;

(* ------------------------------------------------------------------------- *)
(* Symmetric transitive closure                                              *)
(* ------------------------------------------------------------------------- *)

let STC = new_definition
  `STC(R:A->A->bool) = TC(SC R)`;;

let STC_INC = prove
 (`!(R:A->A->bool) x y. R x y ==> STC R x y`,
  REWRITE_TAC[STC] THEN MESON_TAC[SC_INC; TC_INC]);;

let STC_SYM = prove
 (`!(R:A->A->bool) x y. STC R x y ==> STC R y x`,
  REWRITE_TAC[STC] THEN MESON_TAC[TC_SYM; SC_SYM]);;

let STC_TRANS = prove
 (`!(R:A->A->bool) x y z. STC R x y /\ STC R y z ==> STC R x z`,
  REWRITE_TAC[STC; TC_TRANS]);;

let STC_TRANS_L = prove
 (`!(R:A->A->bool) x y z. STC R x y /\ R y z ==> STC R x z`,
  REWRITE_TAC[STC] THEN MESON_TAC[TC_TRANS_L; SC_INC]);;

let STC_TRANS_R = prove
 (`!(R:A->A->bool) x y z. R x y /\ STC R y z ==> STC R x z`,
  REWRITE_TAC[STC] THEN MESON_TAC[TC_TRANS_R; SC_INC]);;

let STC_CASES = prove
 (`!(R:A->A->bool) x z. STC R x z <=> R x z \/ STC R z x \/
                                      ?y. STC R x y /\ STC R y z`,
  REWRITE_TAC[STC] THEN MESON_TAC[SC_SYM; TC_SYM; TC_INC; TC_TRANS; SC_INC]);;

let STC_CASES_L = prove
 (`!(R:A->A->bool) x z. STC R x z <=> R x z \/ STC R z x \/
                                      ?y. STC R x y /\ R y z`,
  REWRITE_TAC[STC] THEN MESON_TAC[SC_SYM; TC_SYM; TC_INC; TC_TRANS; SC_INC]);;

let STC_CASES_R = prove
 (`!(R:A->A->bool) x z. STC R x z <=> R x z \/ STC R z x \/
                                      ?y. R x y /\ STC R y z`,
  REWRITE_TAC[STC] THEN MESON_TAC[SC_SYM; TC_SYM; TC_INC; TC_TRANS; SC_INC]);;

let STC_INDUCT = prove
 (`!(R:A->A->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x y. P x y ==> P y x) /\
        (!x y z. P x y /\ P y z ==> P x z) ==>
                !x y. STC R x y ==> P x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[STC] THEN
  MATCH_MP_TAC TC_INDUCT THEN ASM_MESON_TAC[SC_EXPLICIT]);;

let STC_MONO = prove
 (`!(R:A->A->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. STC R x y ==> STC S x y)`,
  REWRITE_TAC[STC] THEN MESON_TAC[SC_MONO; TC_MONO]);;

let STC_CLOSED = prove
 (`!R:A->A->bool. (STC R = R) <=> (!x y. R x y ==> R y x) /\
                                  (!x y z. R x y /\ R y z ==> R x z)`,
  GEN_TAC THEN REWRITE_TAC[STC; SC_EXPLICIT] THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN MESON_TAC[TC_TRANS; TC_SYM; SC_SYM];
    REWRITE_TAC[GSYM SC_CLOSED; GSYM TC_CLOSED] THEN MESON_TAC[]]);;

let STC_IDEMP = prove
 (`!R:A->A->bool. STC(STC R) = STC R`,
  REWRITE_TAC[STC_CLOSED; STC_SYM; STC_TRANS]);;

let STC_REFL = prove
 (`!R:A->A->bool. (!x. R x x) ==> !x. STC R x x`,
  MESON_TAC[STC_INC]);;

(* ------------------------------------------------------------------------- *)
(* Reflexive symmetric transitive closure (smallest equivalence relation)    *)
(* ------------------------------------------------------------------------- *)

let RSTC = new_definition
  `RSTC(R:A->A->bool) = RC(TC(SC R))`;;

let RSTC_INC = prove
 (`!(R:A->A->bool) x y. R x y ==> RSTC R x y`,
  REWRITE_TAC[RSTC] THEN MESON_TAC[RC_INC; TC_INC; SC_INC]);;

let RSTC_REFL = prove
 (`!(R:A->A->bool) x. RSTC R x x`,
  REWRITE_TAC[RSTC; RC_REFL]);;

let RSTC_SYM = prove
 (`!(R:A->A->bool) x y. RSTC R x y ==> RSTC R y x`,
  REWRITE_TAC[RSTC] THEN MESON_TAC[SC_SYM; TC_SYM; RC_SYM]);;

let RSTC_TRANS = prove
 (`!(R:A->A->bool) x y z. RSTC R x y /\ RSTC R y z ==> RSTC R x z`,
  REWRITE_TAC[RSTC; RC_TC; TC_TRANS]);;

let RSTC_RULES = prove
 (`!(R:A->A->bool).
        (!x y. R x y ==> RSTC R x y) /\
        (!x. RSTC R x x) /\
        (!x y. RSTC R x y ==> RSTC R y x) /\
        (!x y z. RSTC R x y /\ RSTC R y z ==> RSTC R x z)`,
  REWRITE_TAC[RSTC_INC; RSTC_REFL; RSTC_SYM; RSTC_TRANS]);;

let RSTC_TRANS_L = prove
 (`!(R:A->A->bool) x y z. RSTC R x y /\ R y z ==> RSTC R x z`,
  REWRITE_TAC[RSTC; RC_TC] THEN MESON_TAC[TC_TRANS_L; RC_INC; SC_INC]);;

let RSTC_TRANS_R = prove
 (`!(R:A->A->bool) x y z. R x y /\ RSTC R y z ==> RSTC R x z`,
  REWRITE_TAC[RSTC; RC_TC] THEN MESON_TAC[TC_TRANS_R; RC_INC; SC_INC]);;

let RSTC_CASES = prove
 (`!(R:A->A->bool) x z. RSTC R x z <=> (x = z) \/ R x z \/ RSTC R z x \/
                                       ?y. RSTC R x y /\ RSTC R y z`,
  REWRITE_TAC[RSTC; RC_TC; RC_SC] THEN REWRITE_TAC[GSYM STC] THEN
  MESON_TAC[STC_CASES; RC_CASES]);;

let RSTC_CASES_L = prove
 (`!(R:A->A->bool) x z. RSTC R x z <=> (x = z) \/ R x z \/ RSTC R z x \/
                                     ?y. RSTC R x y /\ R y z`,
  REWRITE_TAC[RSTC; RC_TC; RC_SC] THEN REWRITE_TAC[GSYM STC] THEN
  MESON_TAC[STC_CASES_L; RC_CASES]);;

let RSTC_CASES_R = prove
 (`!(R:A->A->bool) x z. RSTC R x z <=> (x = z) \/ R x z \/ RSTC R z x \/
                                       ?y. R x y /\ RSTC R y z`,
  REWRITE_TAC[RSTC; RC_TC; RC_SC] THEN REWRITE_TAC[GSYM STC] THEN
  MESON_TAC[STC_CASES_R; RC_CASES]);;

let RSTC_INDUCT = prove
 (`!(R:A->A->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x. P x x) /\
        (!x y. P x y ==> P y x) /\
        (!x y z. P x y /\ P y z ==> P x z)
        ==> !x y. RSTC R x y ==> P x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[RSTC; RC_TC; RC_SC] THEN REWRITE_TAC[GSYM STC] THEN
  MATCH_MP_TAC STC_INDUCT THEN REWRITE_TAC[RC_EXPLICIT] THEN ASM_MESON_TAC[]);;

let RSTC_MONO = prove
 (`!(R:A->A->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. RSTC R x y ==> RSTC S x y)`,
  REWRITE_TAC[RSTC] THEN MESON_TAC[RC_MONO; SC_MONO; TC_MONO]);;

let RSTC_CLOSED = prove
 (`!R:A->A->bool. (RSTC R = R) <=> (!x. R x x) /\
                                   (!x y. R x y ==> R y x) /\
                                   (!x y z. R x y /\ R y z ==> R x z)`,
  REWRITE_TAC[RSTC] THEN REWRITE_TAC[GSYM STC; GSYM STC_CLOSED] THEN
  REWRITE_TAC[RC_EXPLICIT; FUN_EQ_THM] THEN MESON_TAC[STC_INC]);;

let RSTC_IDEMP = prove
 (`!R:A->A->bool. RSTC(RSTC R) = RSTC R`,
  REWRITE_TAC[RSTC_CLOSED; RSTC_REFL; RSTC_SYM; RSTC_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Finally, we prove the inclusion properties for composite closures         *)
(* ------------------------------------------------------------------------- *)

let RSC_INC_RC = prove
 (`!R:A->A->bool. !x y. RC R x y ==> RSC R x y`,
  REWRITE_TAC[RSC; RC_SC; SC_INC]);;

let RSC_INC_SC = prove
 (`!R:A->A->bool. !x y. SC R x y ==> RSC R x y`,
  REWRITE_TAC[RSC; RC_INC]);;

let RTC_INC_RC = prove
 (`!R:A->A->bool. !x y. RC R x y ==> RTC R x y`,
  REWRITE_TAC[RTC; RC_TC; TC_INC]);;

let RTC_INC_TC = prove
 (`!R:A->A->bool. !x y. TC R x y ==> RTC R x y`,
  REWRITE_TAC[RTC; RC_INC]);;

let STC_INC_SC = prove
 (`!R:A->A->bool. !x y. SC R x y ==> STC R x y`,
  REWRITE_TAC[STC; TC_INC]);;

let STC_INC_TC = prove
 (`!R:A->A->bool. !x y. TC R x y ==> STC R x y`,
  REWRITE_TAC[STC] THEN MESON_TAC[TC_MONO; SC_INC]);;

let RSTC_INC_RC = prove
 (`!R:A->A->bool. !x y. RC R x y ==> RSTC R x y`,
  REWRITE_TAC[RSTC; RC_TC; RC_SC; GSYM STC; STC_INC]);;

let RSTC_INC_SC = prove
 (`!R:A->A->bool. !x y. SC R x y ==> RSTC R x y`,
  REWRITE_TAC[RSTC; GSYM RTC; RTC_INC]);;

let RSTC_INC_TC = prove
 (`!R:A->A->bool. !x y. TC R x y ==> RSTC R x y`,
  REWRITE_TAC[RSTC; RC_TC; GSYM RSC] THEN MESON_TAC[TC_MONO; RSC_INC]);;

let RSTC_INC_RSC = prove
 (`!R:A->A->bool. !x y. RSC R x y ==> RSTC R x y`,
  REWRITE_TAC[RSC; RSTC; RC_TC; TC_INC]);;

let RSTC_INC_RTC = prove
 (`!R:A->A->bool. !x y. RTC R x y ==> RSTC R x y`,
  REWRITE_TAC[GSYM RTC; RSTC] THEN MESON_TAC[RTC_MONO; SC_INC]);;

let RSTC_INC_STC = prove
 (`!R:A->A->bool. !x y. STC R x y ==> RSTC R x y`,
  REWRITE_TAC[GSYM STC; RSTC; RC_INC]);;

(* ------------------------------------------------------------------------- *)
(* Handy things about reverse relations.                                     *)
(* ------------------------------------------------------------------------- *)

let INV = new_definition
  `INV R (x:A) (y:B) <=> R y x`;;

let RC_INV = prove
 (`RC(INV R) = INV(RC R)`,
  REWRITE_TAC[FUN_EQ_THM; RC_EXPLICIT; INV; EQ_SYM_EQ]);;

let SC_INV = prove
 (`SC(INV R) = INV(SC R)`,
  REWRITE_TAC[FUN_EQ_THM; SC_EXPLICIT; INV; DISJ_SYM]);;

let SC_INV_STRONG = prove
 (`SC(INV R) = SC R`,
  REWRITE_TAC[FUN_EQ_THM; SC_EXPLICIT; INV; DISJ_SYM]);;

let TC_INV = prove
 (`TC(INV R) = INV(TC R)`,
  REWRITE_TAC[FUN_EQ_THM; INV] THEN REPEAT GEN_TAC THEN EQ_TAC THEN
  RULE_INDUCT_TAC TC_INDUCT THEN MESON_TAC[INV; TC_RULES]);;

let RSC_INV = prove
 (`RSC(INV R) = INV(RSC R)`,
  REWRITE_TAC[RSC; RC_INV; SC_INV]);;

let RTC_INV = prove
 (`RTC(INV R) = INV(RTC R)`,
  REWRITE_TAC[RTC; RC_INV; TC_INV]);;

let STC_INV = prove
 (`STC(INV R) = INV(STC R)`,
  REWRITE_TAC[STC; SC_INV; TC_INV]);;

let RSTC_INV = prove
 (`RSTC(INV R) = INV(RSTC R)`,
  REWRITE_TAC[RSTC; RC_INV; SC_INV; TC_INV]);;

(* ------------------------------------------------------------------------- *)
(* An iterative version of (R)TC.                                            *)
(* ------------------------------------------------------------------------- *)

let RELPOW = new_recursive_definition num_RECURSION
  `(RELPOW 0 (R:A->A->bool) x y <=> (x = y)) /\
   (RELPOW (SUC n) R x y <=> ?z. RELPOW n R x z /\ R z y)`;;

let RELPOW_R = prove
 (`(RELPOW 0 (R:A->A->bool) x y <=> (x = y)) /\
   (RELPOW (SUC n) R x y <=> ?z. R x z /\ RELPOW n R z y)`,
  CONJ_TAC THENL [REWRITE_TAC[RELPOW]; ALL_TAC] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`x:A`; `y:A`; `n:num`] THEN
  INDUCT_TAC THEN ASM_MESON_TAC[RELPOW]);;

let RELPOW_M = prove
 (`!m n x:A y. RELPOW (m + n) R x y <=> ?z. RELPOW m R x z /\ RELPOW n R z y`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; RELPOW_R; UNWIND_THM1] THEN
  MESON_TAC[]);;

let RTC_RELPOW = prove
 (`!R (x:A) y. RTC R x y <=> ?n. RELPOW n R x y`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [RULE_INDUCT_TAC RTC_INDUCT_L THEN MESON_TAC[RELPOW];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN SPEC_TAC(`y:A`,`y:A`) THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
    REWRITE_TAC[RELPOW] THEN ASM_MESON_TAC[RTC_REFL; RTC_TRANS_L]]);;

let TC_RELPOW = prove
 (`!R (x:A) y. TC R x y <=> ?n. RELPOW (SUC n) R x y`,
  REWRITE_TAC[RELPOW] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_EXISTS_AND_THM; GSYM RTC_RELPOW] THEN
  ONCE_REWRITE_TAC[TC_CASES_L] THEN REWRITE_TAC[RTC; RC_EXPLICIT] THEN
  MESON_TAC[]);;

let RELPOW_SEQUENCE = prove
 (`!R n x y. RELPOW n R x y <=> ?f. (f(0) = x:A) /\ (f(n) = y) /\
                                    !i. i < n ==> R (f i) (f(SUC i))`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[LT; RELPOW] THENL
   [REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `\n:num. y:A` THEN REWRITE_TAC[];
      MESON_TAC[]];
    REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
     [DISJ_CASES_TAC(ARITH_RULE `(n = 0) \/ 0 < n`) THENL
       [EXISTS_TAC `\i. if i = 0 then x else y:A` THEN
        ASM_REWRITE_TAC[ARITH; LT] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[NOT_SUC] THEN
        ASM_MESON_TAC[];
        EXISTS_TAC `\i. if i <= n then f(i) else (y:A)` THEN
        ASM_REWRITE_TAC[LE_0; ARITH_RULE `~(SUC n <= n)`] THEN
        REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC[LE_REFL; ARITH_RULE `~(SUC n <= n)`] THEN
        ASM_REWRITE_TAC[LE_SUC_LT] THEN
        ASM_REWRITE_TAC[LE_LT] THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      EXISTS_TAC `(f:num->A) n` THEN CONJ_TAC THENL
       [EXISTS_TAC `f:num->A` THEN ASM_REWRITE_TAC[] THEN
        REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[]]]]);;
