(* ========================================================================= *)
(* Trivial odds and ends.                                                    *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "class.ml";;

(* ------------------------------------------------------------------------- *)
(* Combinators. We don't bother with S and K, which seem of little use.      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("o",(26,"right"));;

let o_DEF = new_definition
 `(o) (f:B->C) g = \x:A. f(g(x))`;;

let I_DEF = new_definition
 `I = \x:A. x`;;

let o_THM = prove
 (`!f:B->C. !g:A->B. !x:A. (f o g) x = f(g(x))`,
  PURE_REWRITE_TAC [o_DEF] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  REPEAT GEN_TAC THEN REFL_TAC);;

let o_ASSOC = prove
 (`!f:C->D. !g:B->C. !h:A->B. f o (g o h) = (f o g) o h`,
  REPEAT GEN_TAC THEN REWRITE_TAC [o_DEF] THEN
  CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
  REFL_TAC);;

let I_THM = prove
 (`!x:A. I x = x`,
  REWRITE_TAC [I_DEF]);;

let I_O_ID = prove
 (`!f:A->B. (I o f = f) /\ (f o I = f)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_DEF; I_THM]);;

(* ------------------------------------------------------------------------- *)
(* The theory "1" (a 1-element type).                                        *)
(* ------------------------------------------------------------------------- *)

let EXISTS_ONE_REP = prove
 (`?b:bool. b`,
  EXISTS_TAC `T` THEN
  BETA_TAC THEN ACCEPT_TAC TRUTH);;

let one_tydef =
  new_type_definition "1" ("one_ABS","one_REP") EXISTS_ONE_REP;;

let one_DEF = new_definition
 `one = @x:1. T`;;

let one = prove
 (`!v:1. v = one`,
  MP_TAC(GEN_ALL (SPEC `one_REP a` (CONJUNCT2 one_tydef))) THEN
  REWRITE_TAC[CONJUNCT1 one_tydef] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM (CONJUNCT1 one_tydef)] THEN
  ASM_REWRITE_TAC[]);;

let one_axiom = prove
 (`!f g. f = (g:A->1)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[one] THEN REFL_TAC);;

let one_INDUCT = prove
 (`!P. P one ==> !x. P x`,
  ONCE_REWRITE_TAC[one] THEN REWRITE_TAC[]);;

let one_RECURSION = prove
 (`!e:A. ?fn. fn one = e`,
  GEN_TAC THEN EXISTS_TAC `\x:1. e:A` THEN BETA_TAC THEN REFL_TAC);;

let one_Axiom = prove
 (`!e:A. ?!fn. fn one = e`,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM; one_RECURSION] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
  ONCE_REWRITE_TAC [one] THEN ASM_REWRITE_TAC[]);;

let FORALL_ONE_THM = prove
 (`(!x. P x) <=> P one`,
  EQ_TAC THEN REWRITE_TAC[one_INDUCT] THEN DISCH_THEN MATCH_ACCEPT_TAC);;

let EXISTS_ONE_THM = prove
 (`(?x. P x) <=> P one`,
  GEN_REWRITE_TAC I [TAUT `(p <=> q) <=> (~p <=> ~q)`] THEN
  REWRITE_TAC[NOT_EXISTS_THM; FORALL_ONE_THM]);;

let ETA_ONE = prove
 (`!f:1->A. (\x. f one) = f`,
  REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[one] THEN REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Add the type "1" to the inductive type store.                             *)
(* ------------------------------------------------------------------------- *)

inductive_type_store :=
  ("1",(1,one_INDUCT,one_RECURSION))::(!inductive_type_store);;
