(* ========================================================================= *)
(* Additional theorems, mainly about quantifiers, and additional tactics.    *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                 (c) Copyright, Marco Maggesi 2012                         *)
(* ========================================================================= *)

needs "simp.ml";;

(* ------------------------------------------------------------------------- *)
(* More stuff about equality.                                                *)
(* ------------------------------------------------------------------------- *)

let EQ_REFL = prove
 (`!x:A. x = x`,
  GEN_TAC THEN REFL_TAC);;

let REFL_CLAUSE = prove
 (`!x:A. (x = x) <=> T`,
  GEN_TAC THEN MATCH_ACCEPT_TAC(EQT_INTRO(SPEC_ALL EQ_REFL)));;

let EQ_SYM = prove
 (`!(x:A) y. (x = y) ==> (y = x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(ACCEPT_TAC o SYM));;

let EQ_SYM_EQ = prove
 (`!(x:A) y. (x = y) <=> (y = x)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN MATCH_ACCEPT_TAC EQ_SYM);;

let EQ_TRANS = prove
 (`!(x:A) y z. (x = y) /\ (y = z) ==> (x = z)`,
  REPEAT STRIP_TAC THEN PURE_ASM_REWRITE_TAC[] THEN REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* The following is a common special case of ordered rewriting.              *)
(* ------------------------------------------------------------------------- *)

let AC acsuite = EQT_ELIM o PURE_REWRITE_CONV[acsuite; REFL_CLAUSE];;

(* ------------------------------------------------------------------------- *)
(* A couple of theorems about beta reduction.                                *)
(* ------------------------------------------------------------------------- *)

let BETA_THM = prove
 (`!(f:A->B) y. (\x. (f:A->B) x) y = f y`,
  REPEAT GEN_TAC THEN BETA_TAC THEN REFL_TAC);;

let ABS_SIMP = prove
 (`!(t1:A) (t2:B). (\x. t1) t2 = t1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BETA_THM; REFL_CLAUSE]);;

(* ------------------------------------------------------------------------- *)
(* A few "big name" intuitionistic tautologies.                              *)
(* ------------------------------------------------------------------------- *)

let CONJ_ASSOC = prove
 (`!t1 t2 t3. t1 /\ t2 /\ t3 <=> (t1 /\ t2) /\ t3`,
  ITAUT_TAC);;

let CONJ_SYM = prove
 (`!t1 t2. t1 /\ t2 <=> t2 /\ t1`,
  ITAUT_TAC);;

let CONJ_ACI = prove
 (`(p /\ q <=> q /\ p) /\
   ((p /\ q) /\ r <=> p /\ (q /\ r)) /\
   (p /\ (q /\ r) <=> q /\ (p /\ r)) /\
   (p /\ p <=> p) /\
   (p /\ (p /\ q) <=> p /\ q)`,
  ITAUT_TAC);;

let DISJ_ASSOC = prove
 (`!t1 t2 t3. t1 \/ t2 \/ t3 <=> (t1 \/ t2) \/ t3`,
  ITAUT_TAC);;

let DISJ_SYM = prove
 (`!t1 t2. t1 \/ t2 <=> t2 \/ t1`,
  ITAUT_TAC);;

let DISJ_ACI = prove
 (`(p \/ q <=> q \/ p) /\
   ((p \/ q) \/ r <=> p \/ (q \/ r)) /\
   (p \/ (q \/ r) <=> q \/ (p \/ r)) /\
   (p \/ p <=> p) /\
   (p \/ (p \/ q) <=> p \/ q)`,
  ITAUT_TAC);;

let IMP_CONJ = prove
 (`p /\ q ==> r <=> p ==> q ==> r`,
  ITAUT_TAC);;

let IMP_IMP = GSYM IMP_CONJ;;

let IMP_CONJ_ALT = prove
 (`p /\ q ==> r <=> q ==> p ==> r`,
  ITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* A couple of "distribution" tautologies are useful.                        *)
(* ------------------------------------------------------------------------- *)

let LEFT_OR_DISTRIB = prove
 (`!p q r. p /\ (q \/ r) <=> p /\ q \/ p /\ r`,
  ITAUT_TAC);;

let RIGHT_OR_DISTRIB = prove
 (`!p q r. (p \/ q) /\ r <=> p /\ r \/ q /\ r`,
  ITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Degenerate cases of quantifiers.                                          *)
(* ------------------------------------------------------------------------- *)

let FORALL_SIMP = prove
 (`!t. (!x:A. t) = t`,
  ITAUT_TAC);;

let EXISTS_SIMP = prove
 (`!t. (?x:A. t) = t`,
  ITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* I also use this a lot (as a prelude to congruence reasoning).             *)
(* ------------------------------------------------------------------------- *)

let EQ_IMP = ITAUT `(a <=> b) ==> a ==> b`;;

(* ------------------------------------------------------------------------- *)
(* Start building up the basic rewrites; we add a few more later.            *)
(* ------------------------------------------------------------------------- *)

let EQ_CLAUSES = prove
 (`!t. ((T <=> t) <=> t) /\ ((t <=> T) <=> t) /\
       ((F <=> t) <=> ~t) /\ ((t <=> F) <=> ~t)`,
  ITAUT_TAC);;

let NOT_CLAUSES_WEAK = prove
 (`(~T <=> F) /\ (~F <=> T)`,
  ITAUT_TAC);;

let AND_CLAUSES = prove
 (`!t. (T /\ t <=> t) /\ (t /\ T <=> t) /\ (F /\ t <=> F) /\
       (t /\ F <=> F) /\ (t /\ t <=> t)`,
  ITAUT_TAC);;

let OR_CLAUSES = prove
 (`!t. (T \/ t <=> T) /\ (t \/ T <=> T) /\ (F \/ t <=> t) /\
       (t \/ F <=> t) /\ (t \/ t <=> t)`,
  ITAUT_TAC);;

let IMP_CLAUSES = prove
 (`!t. (T ==> t <=> t) /\ (t ==> T <=> T) /\ (F ==> t <=> T) /\
       (t ==> t <=> T) /\ (t ==> F <=> ~t)`,
  ITAUT_TAC);;

extend_basic_rewrites
  [REFL_CLAUSE;
   EQ_CLAUSES;
   NOT_CLAUSES_WEAK;
   AND_CLAUSES;
   OR_CLAUSES;
   IMP_CLAUSES;
   FORALL_SIMP;
   EXISTS_SIMP;
   BETA_THM;
   let IMP_EQ_CLAUSE = prove
    (`((x = x) ==> p) <=> p`,
     REWRITE_TAC[EQT_INTRO(SPEC_ALL EQ_REFL); IMP_CLAUSES]) in
   IMP_EQ_CLAUSE];;

extend_basic_congs
  [ITAUT `(p <=> p') ==> (p' ==> (q <=> q')) ==> (p ==> q <=> p' ==> q')`];;

(* ------------------------------------------------------------------------- *)
(* Rewrite rule for unique existence.                                        *)
(* ------------------------------------------------------------------------- *)

let EXISTS_UNIQUE_THM = prove
 (`!P. (?!x:A. P x) <=> (?x. P x) /\ (!x x'. P x /\ P x' ==> (x = x'))`,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Trivial instances of existence.                                           *)
(* ------------------------------------------------------------------------- *)

let EXISTS_REFL = prove
 (`!a:A. ?x. x = a`,
  GEN_TAC THEN EXISTS_TAC `a:A` THEN REFL_TAC);;

let EXISTS_UNIQUE_REFL = prove
 (`!a:A. ?!x. x = a`,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  REPEAT(EQ_TAC ORELSE STRIP_TAC) THENL
   [EXISTS_TAC `a:A`; ASM_REWRITE_TAC[]] THEN
  REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Unwinding.                                                                *)
(* ------------------------------------------------------------------------- *)

let UNWIND_THM1 = prove
 (`!P (a:A). (?x. a = x /\ P x) <=> P a`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC ACCEPT_TAC));
    DISCH_TAC THEN EXISTS_TAC `a:A` THEN
    CONJ_TAC THEN TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN
    REFL_TAC]);;

let UNWIND_THM2 = prove
 (`!P (a:A). (?x. x = a /\ P x) <=> P a`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  MATCH_ACCEPT_TAC UNWIND_THM1);;

let FORALL_UNWIND_THM2 = prove
 (`!P (a:A). (!x. x = a ==> P x) <=> P a`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `a:A`) THEN REWRITE_TAC[];
    DISCH_TAC THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[]]);;

let FORALL_UNWIND_THM1 = prove
 (`!P (a:A). (!x. a = x ==> P x) <=> P a`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  MATCH_ACCEPT_TAC FORALL_UNWIND_THM2);;

(* ------------------------------------------------------------------------- *)
(* Permuting quantifiers.                                                    *)
(* ------------------------------------------------------------------------- *)

let SWAP_FORALL_THM = prove
 (`!P:A->B->bool. (!x y. P x y) <=> (!y x. P x y)`,
  ITAUT_TAC);;

let SWAP_EXISTS_THM = prove
 (`!P:A->B->bool. (?x y. P x y) <=> (?y x. P x y)`,
  ITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Universal quantifier and conjunction.                                     *)
(* ------------------------------------------------------------------------- *)

let FORALL_AND_THM = prove
 (`!P Q. (!x:A. P x /\ Q x) <=> (!x. P x) /\ (!x. Q x)`,
  ITAUT_TAC);;

let AND_FORALL_THM = prove
 (`!P Q. (!x. P x) /\ (!x. Q x) <=> (!x:A. P x /\ Q x)`,
  ITAUT_TAC);;

let LEFT_AND_FORALL_THM = prove
 (`!P Q. (!x:A. P x) /\ Q <=> (!x:A. P x /\ Q)`,
  ITAUT_TAC);;

let RIGHT_AND_FORALL_THM = prove
 (`!P Q. P /\ (!x:A. Q x) <=> (!x. P /\ Q x)`,
  ITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Existential quantifier and disjunction.                                   *)
(* ------------------------------------------------------------------------- *)

let EXISTS_OR_THM = prove
 (`!P Q. (?x:A. P x \/ Q x) <=> (?x. P x) \/ (?x. Q x)`,
  ITAUT_TAC);;

let OR_EXISTS_THM = prove
 (`!P Q. (?x. P x) \/ (?x. Q x) <=> (?x:A. P x \/ Q x)`,
  ITAUT_TAC);;

let LEFT_OR_EXISTS_THM = prove
 (`!P Q. (?x. P x) \/ Q <=> (?x:A. P x \/ Q)`,
  ITAUT_TAC);;

let RIGHT_OR_EXISTS_THM = prove
 (`!P Q. P \/ (?x. Q x) <=> (?x:A. P \/ Q x)`,
  ITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Existential quantifier and conjunction.                                   *)
(* ------------------------------------------------------------------------- *)

let LEFT_EXISTS_AND_THM = prove
 (`!P Q. (?x:A. P x /\ Q) <=> (?x:A. P x) /\ Q`,
  ITAUT_TAC);;

let RIGHT_EXISTS_AND_THM = prove
 (`!P Q. (?x:A. P /\ Q x) <=> P /\ (?x:A. Q x)`,
  ITAUT_TAC);;

let TRIV_EXISTS_AND_THM = prove
 (`!P Q. (?x:A. P /\ Q) <=> (?x:A. P) /\ (?x:A. Q)`,
  ITAUT_TAC);;

let LEFT_AND_EXISTS_THM = prove
 (`!P Q. (?x:A. P x) /\ Q <=> (?x:A. P x /\ Q)`,
  ITAUT_TAC);;

let RIGHT_AND_EXISTS_THM = prove
 (`!P Q. P /\ (?x:A. Q x) <=> (?x:A. P /\ Q x)`,
  ITAUT_TAC);;

let TRIV_AND_EXISTS_THM = prove
 (`!P Q. (?x:A. P) /\ (?x:A. Q) <=> (?x:A. P /\ Q)`,
  ITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Only trivial instances of universal quantifier and disjunction.           *)
(* ------------------------------------------------------------------------- *)

let TRIV_FORALL_OR_THM = prove
 (`!P Q. (!x:A. P \/ Q) <=> (!x:A. P) \/ (!x:A. Q)`,
  ITAUT_TAC);;

let TRIV_OR_FORALL_THM = prove
 (`!P Q. (!x:A. P) \/ (!x:A. Q) <=> (!x:A. P \/ Q)`,
  ITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Implication and quantifiers.                                              *)
(* ------------------------------------------------------------------------- *)

let RIGHT_IMP_FORALL_THM = prove
 (`!P Q. (P ==> !x:A. Q x) <=> (!x. P ==> Q x)`,
  ITAUT_TAC);;

let RIGHT_FORALL_IMP_THM = prove
 (`!P Q. (!x. P ==> Q x) <=> (P ==> !x:A. Q x)`,
  ITAUT_TAC);;

let LEFT_IMP_EXISTS_THM = prove
 (`!P Q. ((?x:A. P x) ==> Q) <=> (!x. P x ==> Q)`,
  ITAUT_TAC);;

let LEFT_FORALL_IMP_THM = prove
 (`!P Q. (!x. P x ==> Q) <=> ((?x:A. P x) ==> Q)`,
  ITAUT_TAC);;

let TRIV_FORALL_IMP_THM = prove
 (`!P Q. (!x:A. P ==> Q) <=> ((?x:A. P) ==> (!x:A. Q))`,
  ITAUT_TAC);;

let TRIV_EXISTS_IMP_THM = prove
 (`!P Q. (?x:A. P ==> Q) <=> ((!x:A. P) ==> (?x:A. Q))`,
  ITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Monotonicity theorems for logical operations w.r.t. implication.          *)
(* ------------------------------------------------------------------------- *)

let MONO_AND = ITAUT `(A ==> B) /\ (C ==> D) ==> (A /\ C ==> B /\ D)`;;

let MONO_OR = ITAUT `(A ==> B) /\ (C ==> D) ==> (A \/ C ==> B \/ D)`;;

let MONO_IMP = ITAUT `(B ==> A) /\ (C ==> D) ==> ((A ==> C) ==> (B ==> D))`;;

let MONO_NOT = ITAUT `(B ==> A) ==> (~A ==> ~B)`;;

let MONO_FORALL = prove
 (`(!x:A. P x ==> Q x) ==> ((!x. P x) ==> (!x. Q x))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let MONO_EXISTS = prove
 (`(!x:A. P x ==> Q x) ==> ((?x. P x) ==> (?x. Q x))`,
  DISCH_TAC THEN DISCH_THEN(X_CHOOSE_TAC `x:A`) THEN
  EXISTS_TAC `x:A` THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A generic "without loss of generality" lemma for symmetry.                *)
(* ------------------------------------------------------------------------- *)

let WLOG_RELATION = prove
 (`!R P. (!x y. P x y ==> P y x) /\
         (!x y. R x y \/ R y x) /\
         (!x y. R x y ==> P x y)
         ==> !x y:A. P x y`,
  REPEAT GEN_TAC THEN DISCH_THEN
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Alternative versions of unique existence.                                 *)
(* ------------------------------------------------------------------------- *)

let EXISTS_UNIQUE_ALT = prove
 (`!P:A->bool. (?!x. P x) <=> (?x. !y. P y <=> (x = y))`,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `x:A`) ASSUME_TAC) THEN
    EXISTS_TAC `x:A` THEN GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_ACCEPT_TAC];
    DISCH_THEN(X_CHOOSE_TAC `x:A`) THEN
    ASM_REWRITE_TAC[GSYM EXISTS_REFL] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN REFL_TAC]);;

let EXISTS_UNIQUE = prove
 (`!P:A->bool. (?!x. P x) <=> (?x. P x /\ !y. P y ==> (y = x))`,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_ALT] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV)
   [ITAUT `(a <=> b) <=> (a ==> b) /\ (b ==> a)`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN SIMP_TAC[] THEN
  REWRITE_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  REWRITE_TAC[CONJ_ACI]);;

(* ------------------------------------------------------------------------- *)
(* DESTRUCT_TAC, FIX_TAC, INTRO_TAC and HYP_TAC, giving more brief and       *)
(* elegant ways of naming introduced variables and assumptions (from Marco   *)
(* Maggesi).                                                                 *)
(* ------------------------------------------------------------------------- *)

let DESTRUCT_TAC,FIX_TAC,INTRO_TAC,HYP_TAC =
  (* ---------------------------------------------------------------------- *)
  (* Like GEN_TAC but fails instead of generating a primed variant when the *)
  (* variable occurs free in the context.                                   *)
  (* ---------------------------------------------------------------------- *)
  let (PURE_GEN_TAC: tactic) =
    fun (asl,w) ->
      try let x = fst(dest_forall w) in
          let avoids = itlist (union o thm_frees o snd) asl (frees w) in
          if mem x avoids then fail() else X_GEN_TAC x (asl,w)
      with Failure _ -> failwith "PURE_GEN_TAC"
  (* ---------------------------------------------------------------------- *)
  (* Like X_GEN_TAC but needs only the name of the variable, not the type.  *)
  (* ---------------------------------------------------------------------- *)
  and (NAME_GEN_TAC: string -> tactic) =
    fun s gl ->
      let ty = (snd o dest_var o fst o dest_forall o snd) gl  in
      X_GEN_TAC (mk_var(s,ty)) gl
  and OBTAIN_THEN v ttac th =
    let ty = (snd o dest_var o fst o dest_exists o concl) th in
    X_CHOOSE_THEN (mk_var(v,ty)) ttac th
  and CONJ_LIST_TAC = end_itlist (fun t1 t2 -> CONJ_TAC THENL [t1; t2])
  and NUM_DISJ_TAC n =
    if n <= 0 then failwith "NUM_DISJ_TAC" else
    REPLICATE_TAC (n-1) DISJ2_TAC THEN REPEAT DISJ1_TAC
  and NAME_PULL_FORALL_CONV =
    let SWAP_FORALL_CONV = REWR_CONV SWAP_FORALL_THM
    and AND_FORALL_CONV = GEN_REWRITE_CONV I [AND_FORALL_THM]
    and RIGHT_IMP_FORALL_CONV = GEN_REWRITE_CONV I [RIGHT_IMP_FORALL_THM] in
    fun s ->
      let rec PULL_FORALL tm =
          if is_forall tm then
            if name_of(fst(dest_forall tm)) = s then REFL tm else
              (BINDER_CONV PULL_FORALL THENC SWAP_FORALL_CONV) tm
          else if is_imp tm then
            (RAND_CONV PULL_FORALL THENC RIGHT_IMP_FORALL_CONV) tm
          else if is_conj tm then
            (BINOP_CONV PULL_FORALL THENC AND_FORALL_CONV) tm
          else
            fail () in
      PULL_FORALL in
  let pa_ident p = function
      Ident s::rest when p s -> s,rest
    | _ -> raise Noparse in
  let pa_label = pa_ident isalnum
  and pa_var = pa_ident isalpha in
  let fix_tac =
    let fix_var v = CONV_TAC (NAME_PULL_FORALL_CONV v) THEN PURE_GEN_TAC
    and fix_rename =
      function u,[v] -> CONV_TAC (NAME_PULL_FORALL_CONV v) THEN NAME_GEN_TAC u
             | u,_   -> NAME_GEN_TAC u in
    let vars =
      let pa_rename =
        let oname = possibly (a(Ident "/") ++ pa_var >> snd) in
        (a(Resword "[") ++ pa_var >> snd) ++ oname ++ a(Resword "]") >> fst in
      many ((pa_rename >> fix_rename) ||| (pa_var >> fix_var)) >> EVERY
    and star = possibly (a (Ident "*") >> K ()) in
    vars ++ star >> function tac,[] -> tac | tac,_ -> tac THEN REPEAT GEN_TAC
  and destruct_tac =
    let OBTAINL_THEN : string list -> thm_tactical =
      EVERY_TCL o map OBTAIN_THEN in
    let rec destruct inp = disj inp
    and disj inp =
      let DISJ_CASES_LIST = end_itlist DISJ_CASES_THEN2 in
      (listof conj (a(Resword "|")) "Disjunction" >> DISJ_CASES_LIST) inp
    and conj inp = (atleast 1 atom >> end_itlist CONJUNCTS_THEN2) inp
    and obtain inp =
      let obtain_prfx =
        let var_list = atleast 1 pa_var in
        (a(Ident "@") ++ var_list >> snd) ++ a(Resword ".") >> fst in
      (obtain_prfx ++ destruct >> uncurry OBTAINL_THEN) inp
    and atom inp =
      let label =
        function Ident "_"::res -> K ALL_TAC,res
               | Ident "+"::res -> MP_TAC,res
               | Ident s::res when isalnum s -> LABEL_TAC s,res
               | _ -> raise Noparse
      and paren =
        (a(Resword "(") ++ destruct >> snd) ++ a(Resword ")") >> fst in
      (obtain ||| label ||| paren) inp in
    destruct in
  let intro_tac =
    let number = function
        Ident s::rest ->
          (try check ((<=) 1) (int_of_string s), rest
           with Failure _ -> raise Noparse)
      | _ -> raise Noparse
    and pa_fix = a(Ident "!") ++ fix_tac >> snd
    and pa_dest = destruct_tac >> DISCH_THEN in
    let pa_prefix =
      elistof (pa_fix ||| pa_dest) (a(Resword ";")) "Prefix intro pattern" in
    let rec pa_intro toks =
      (pa_prefix ++ possibly pa_postfix >> uncurry (@) >> EVERY) toks
    and pa_postfix toks = (pa_conj ||| pa_disj) toks
    and pa_conj toks =
      let conjs =
        listof pa_intro (a(Ident "&")) "Intro pattern" >> CONJ_LIST_TAC in
      ((a(Resword "{") ++ conjs >> snd) ++ a(Resword "}") >> fst) toks
    and pa_disj toks =
      let disj = number >> NUM_DISJ_TAC in
      ((a(Ident "#") ++ disj >> snd) ++ pa_intro >> uncurry (THEN)) toks in
    pa_intro in
  let hyp_tac rule =
    let pa_action = function
        Resword ":" :: rest -> REMOVE_THEN,rest
      | Resword "->" :: rest -> USE_THEN,rest
      | _ -> raise Noparse in
    pa_label ++ possibly (pa_action ++ destruct_tac) >>
    (function
       | lbl,[action,tac] -> action lbl (tac o rule)
       | lbl,_ -> REMOVE_THEN lbl (LABEL_TAC lbl o rule)) in
  let DESTRUCT_TAC s =
    let tac,rest =
      (fix "Destruct pattern" destruct_tac o lex o explode) s in
    if rest=[] then tac else failwith "Garbage after destruct pattern"
  and INTRO_TAC s =
    let tac,rest =
      (fix "Introduction pattern" intro_tac o lex o explode) s in
    if rest=[] then tac else failwith "Garbage after intro pattern"
  and FIX_TAC s =
    let tac,rest = (fix_tac o lex o explode) s in
    if rest=[] then tac else failwith "FIX_TAC: invalid pattern"
  and HYP_TAC s rule =
    let tac,rest = (hyp_tac rule o lex o explode) s in
    if rest=[] then tac else failwith "HYP_TAC: invalid pattern" in
  DESTRUCT_TAC,FIX_TAC,INTRO_TAC,HYP_TAC;;

let CLAIM_TAC s tm = SUBGOAL_THEN tm (DESTRUCT_TAC s);;
