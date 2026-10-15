(* ========================================================================= *)
(* Theory of integers.                                                       *)
(*                                                                           *)
(* The integers are carved out of the real numbers; hence all the            *)
(* universal theorems can be derived trivially from the real analog.         *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "calc_rat.ml";;

(* ------------------------------------------------------------------------- *)
(* Representing predicate. The "is_int" variant is useful for backwards      *)
(* compatibility with former definition of "is_int" constant, now removed.   *)
(* ------------------------------------------------------------------------- *)

let integer = new_definition
  `integer(x) <=> ?n. abs(x) = &n`;;

let is_int = prove
 (`integer(x) <=> ?n. x = &n \/ x = -- &n`,
  REWRITE_TAC[integer] THEN AP_TERM_TAC THEN ABS_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Type of integers.                                                         *)
(* ------------------------------------------------------------------------- *)

let int_tybij = new_type_definition "int" ("int_of_real","real_of_int")
 (prove(`?x. integer x`,
       EXISTS_TAC `&0` THEN
       REWRITE_TAC[is_int; REAL_OF_NUM_EQ; EXISTS_OR_THM; GSYM EXISTS_REFL]));;

let int_abstr,int_rep =
  SPEC_ALL(CONJUNCT1 int_tybij),SPEC_ALL(CONJUNCT2 int_tybij);;

let dest_int_rep = prove
 (`!i. ?n. (real_of_int i = &n) \/ (real_of_int i = --(&n))`,
  REWRITE_TAC[GSYM is_int; int_rep; int_abstr]);;

let INTEGER_REAL_OF_INT = prove
 (`!x. integer(real_of_int x)`,
  MESON_TAC[int_tybij]);;

(* ------------------------------------------------------------------------- *)
(* We want the following too.                                                *)
(* ------------------------------------------------------------------------- *)

let int_eq = prove
 (`!x y. (x = y) <=> (real_of_int x = real_of_int y)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(MP_TAC o AP_TERM `int_of_real`) THEN
  REWRITE_TAC[int_abstr]);;

(* ------------------------------------------------------------------------- *)
(* Set up interface map.                                                     *)
(* ------------------------------------------------------------------------- *)

do_list overload_interface
 ["+",`int_add:int->int->int`; "-",`int_sub:int->int->int`;
  "*",`int_mul:int->int->int`; "<",`int_lt:int->int->bool`;
  "<=",`int_le:int->int->bool`; ">",`int_gt:int->int->bool`;
  ">=",`int_ge:int->int->bool`; "--",`int_neg:int->int`;
  "pow",`int_pow:int->num->int`; "abs",`int_abs:int->int`;
  "max",`int_max:int->int->int`; "min",`int_min:int->int->int`;
  "&",`int_of_num:num->int`];;

let prioritize_int() = prioritize_overload(mk_type("int",[]));;

(* ------------------------------------------------------------------------- *)
(* Definitions and closure derivations of all operations but "inv" and "/".  *)
(* ------------------------------------------------------------------------- *)

let int_le = new_definition
  `x <= y <=> (real_of_int x) <= (real_of_int y)`;;

let int_lt = new_definition
  `x < y <=> (real_of_int x) < (real_of_int y)`;;

let int_ge = new_definition
  `x >= y <=> (real_of_int x) >= (real_of_int y)`;;

let int_gt = new_definition
  `x > y <=> (real_of_int x) > (real_of_int y)`;;

let int_of_num = new_definition
  `&n = int_of_real(real_of_num n)`;;

let int_of_num_th = prove
 (`!n. real_of_int(int_of_num n) = real_of_num n`,
  REWRITE_TAC[int_of_num; GSYM int_rep; is_int] THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; EXISTS_OR_THM; GSYM EXISTS_REFL]);;

let int_neg = new_definition
 `--i = int_of_real(--(real_of_int i))`;;

let int_neg_th = prove
 (`!x. real_of_int(int_neg x) = --(real_of_int x)`,
  REWRITE_TAC[int_neg; GSYM int_rep; is_int] THEN
  GEN_TAC THEN STRIP_ASSUME_TAC(SPEC `x:int` dest_int_rep) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG; EXISTS_OR_THM; REAL_EQ_NEG2;
    REAL_OF_NUM_EQ; GSYM EXISTS_REFL]);;

let int_add = new_definition
 `x + y = int_of_real((real_of_int x) + (real_of_int y))`;;

let int_add_th = prove
 (`!x y. real_of_int(x + y) = (real_of_int x) + (real_of_int y)`,
  REWRITE_TAC[int_add; GSYM int_rep; is_int] THEN REPEAT GEN_TAC THEN
  X_CHOOSE_THEN `m:num` DISJ_CASES_TAC (SPEC `x:int` dest_int_rep) THEN
  X_CHOOSE_THEN `n:num` DISJ_CASES_TAC (SPEC `y:int` dest_int_rep) THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ; EXISTS_OR_THM] THEN
  REWRITE_TAC[GSYM EXISTS_REFL] THEN
  DISJ_CASES_THEN MP_TAC (SPECL [`m:num`; `n:num`] LE_CASES) THEN
  REWRITE_TAC[LE_EXISTS] THEN DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; OR_EXISTS_THM; REAL_NEG_ADD] THEN
  TRY(EXISTS_TAC `d:num` THEN REAL_ARITH_TAC) THEN
  REWRITE_TAC[EXISTS_OR_THM; GSYM REAL_NEG_ADD; REAL_EQ_NEG2;
    REAL_OF_NUM_ADD; REAL_OF_NUM_EQ; GSYM EXISTS_REFL]);;

let int_sub = new_definition
  `x - y = int_of_real(real_of_int x - real_of_int y)`;;

let int_sub_th = prove
 (`!x y. real_of_int(x - y) = (real_of_int x) - (real_of_int y)`,
  REWRITE_TAC[int_sub; real_sub; GSYM int_neg_th; GSYM int_add_th] THEN
  REWRITE_TAC[int_abstr]);;

let int_mul = new_definition
  `x * y = int_of_real ((real_of_int x) * (real_of_int y))`;;

let int_mul_th = prove
 (`!x y. real_of_int(x * y) = (real_of_int x) * (real_of_int y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_mul; GSYM int_rep; is_int] THEN
  X_CHOOSE_THEN `m:num` DISJ_CASES_TAC (SPEC `x:int` dest_int_rep) THEN
  X_CHOOSE_THEN `n:num` DISJ_CASES_TAC (SPEC `y:int` dest_int_rep) THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ; EXISTS_OR_THM] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG; REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[REAL_EQ_NEG2; REAL_OF_NUM_EQ; GSYM EXISTS_REFL]);;

let int_abs = new_definition
  `abs x = int_of_real(abs(real_of_int x))`;;

let int_abs_th = prove
 (`!x. real_of_int(abs x) = abs(real_of_int x)`,
  GEN_TAC THEN REWRITE_TAC[int_abs; real_abs] THEN COND_CASES_TAC THEN
  REWRITE_TAC[GSYM int_neg; int_neg_th; int_abstr]);;

let int_sgn = new_definition
  `int_sgn x = int_of_real(real_sgn(real_of_int x))`;;

let int_sgn_th = prove
 (`!x. real_of_int(int_sgn x) = real_sgn(real_of_int x)`,
  GEN_TAC THEN REWRITE_TAC[int_sgn; real_sgn; GSYM int_rep] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  MESON_TAC[is_int]);;

let int_max = new_definition
  `int_max x y = int_of_real(max (real_of_int x) (real_of_int y))`;;

let int_max_th = prove
 (`!x y. real_of_int(max x y) = max (real_of_int x) (real_of_int y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_max; real_max] THEN
  COND_CASES_TAC THEN REWRITE_TAC[int_abstr]);;

let int_min = new_definition
  `int_min x y = int_of_real(min (real_of_int x) (real_of_int y))`;;

let int_min_th = prove
 (`!x y. real_of_int(min x y) = min (real_of_int x) (real_of_int y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_min; real_min] THEN
  COND_CASES_TAC THEN REWRITE_TAC[int_abstr]);;

let int_pow = new_definition
  `x pow n = int_of_real((real_of_int x) pow n)`;;

let int_pow_th = prove
 (`!x n. real_of_int(x pow n) = (real_of_int x) pow n`,
  GEN_TAC THEN REWRITE_TAC[int_pow] THEN INDUCT_TAC THEN
  REWRITE_TAC[real_pow] THENL
   [REWRITE_TAC[GSYM int_of_num; int_of_num_th];
    POP_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[GSYM int_mul; int_mul_th]]);;

(* ------------------------------------------------------------------------- *)
(* All collected into a single rewrite                                       *)
(* ------------------------------------------------------------------------- *)

let REAL_OF_INT_CLAUSES = prove
 (`(!x y. real_of_int x = real_of_int y <=> x = y) /\
   (!x y. real_of_int x >= real_of_int y <=> x >= y) /\
   (!x y. real_of_int x > real_of_int y <=> x > y) /\
   (!x y. real_of_int x <= real_of_int y <=> x <= y) /\
   (!x y. real_of_int x < real_of_int y <=> x < y) /\
   (!x y. max (real_of_int x) (real_of_int y) = real_of_int(max x y)) /\
   (!x y. min (real_of_int x) (real_of_int y) = real_of_int(min x y)) /\
   (!n. &n = real_of_int(&n)) /\
   (!x. --real_of_int x = real_of_int(--x)) /\
   (!x. abs(real_of_int x) = real_of_int(abs x)) /\
   (!x y. max (real_of_int x) (real_of_int y) = real_of_int(max x y)) /\
   (!x y. min (real_of_int x) (real_of_int y) = real_of_int(min x y)) /\
   (!x. real_sgn (real_of_int x) = real_of_int(int_sgn x)) /\
   (!x y. real_of_int x + real_of_int y = real_of_int(x + y)) /\
   (!x y. real_of_int x - real_of_int y = real_of_int(x - y)) /\
   (!x y. real_of_int x * real_of_int y = real_of_int(x * y)) /\
   (!x n. real_of_int x pow n = real_of_int(x pow n))`,
  REWRITE_TAC[int_eq; int_ge; int_gt; int_le; int_lt; int_max_th; int_min_th;
              int_of_num_th; int_neg_th; int_abs_th; int_max_th; int_min_th;
              int_sgn_th;  int_add_th; int_sub_th; int_mul_th; int_pow_th]);;

(* ------------------------------------------------------------------------- *)
(* A few convenient theorems about the integer type.                         *)
(* ------------------------------------------------------------------------- *)

let INT_IMAGE = prove
 (`!x. (?n. x = &n) \/ (?n. x = --(&n))`,
  GEN_TAC THEN
  X_CHOOSE_THEN `n:num` DISJ_CASES_TAC (SPEC `x:int` dest_int_rep) THEN
  POP_ASSUM(MP_TAC o AP_TERM `int_of_real`) THEN REWRITE_TAC[int_abstr] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[int_of_num; int_neg] THENL
   [DISJ1_TAC; DISJ2_TAC] THEN
  EXISTS_TAC `n:num` THEN REWRITE_TAC[int_abstr] THEN
  REWRITE_TAC[GSYM int_of_num; int_of_num_th]);;

let FORALL_INT_CASES = prove
 (`!P:int->bool. (!x. P x) <=> (!n. P(&n)) /\ (!n. P(-- &n))`,
  MESON_TAC[INT_IMAGE]);;

let EXISTS_INT_CASES = prove
 (`!P:int->bool. (?x. P x) <=> (?n. P(&n)) \/ (?n. P(-- &n))`,
  MESON_TAC[INT_IMAGE]);;

let INT_LT_DISCRETE = prove
 (`!x y. x < y <=> (x + &1) <= y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[int_le; int_lt; int_add_th] THEN
  DISJ_CASES_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC )
   (SPEC `x:int` INT_IMAGE) THEN
  DISJ_CASES_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC )
   (SPEC `y:int` INT_IMAGE) THEN
  REWRITE_TAC[int_neg_th; int_of_num_th] THEN
  REWRITE_TAC[REAL_LE_NEG2; REAL_LT_NEG2] THEN
  REWRITE_TAC[REAL_LE_LNEG; REAL_LT_LNEG; REAL_LE_RNEG; REAL_LT_RNEG] THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[GSYM real_sub; REAL_LE_SUB_RADD] THEN
  REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM ADD1; ONCE_REWRITE_RULE[ADD_SYM] (GSYM ADD1)] THEN
  REWRITE_TAC[SYM(REWRITE_CONV[ARITH_SUC] `SUC 0`)] THEN
  REWRITE_TAC[ADD_CLAUSES; LE_SUC_LT; LT_SUC_LE]);;

let INT_GT_DISCRETE = prove
 (`!x y. x > y <=> x >= (y + &1)`,
  REWRITE_TAC[int_gt; int_ge; real_ge; real_gt; GSYM int_le; GSYM int_lt] THEN
  MATCH_ACCEPT_TAC INT_LT_DISCRETE);;

(* ------------------------------------------------------------------------- *)
(* Conversions of integer constants to and from OCaml numbers.               *)
(* ------------------------------------------------------------------------- *)

let is_intconst tm =
  match tm with
    Comb(Const("int_of_num",_),n) -> is_numeral n
  | Comb(Const("int_neg",_),Comb(Const("int_of_num",_),n)) ->
      is_numeral n && not(dest_numeral n =/ num_0)
  | _ -> false;;

let dest_intconst tm =
  match tm with
    Comb(Const("int_of_num",_),n) -> dest_numeral n
  | Comb(Const("int_neg",_),Comb(Const("int_of_num",_),n)) ->
        let nn = dest_numeral n in
        if nn <>/ num_0 then minus_num(dest_numeral n)
        else failwith "dest_intconst"
  | _ -> failwith "dest_intconst";;

let mk_intconst =
  let cast_tm = `int_of_num` and neg_tm = `int_neg` in
  let mk_numconst n = mk_comb(cast_tm,mk_numeral n) in
  fun x -> if x </ num_0 then mk_comb(neg_tm,mk_numconst(minus_num x))
           else mk_numconst x;;

(* ------------------------------------------------------------------------- *)
(* A simple procedure to lift most universal real theorems to integers.      *)
(* For a more complete procedure, give required term to INT_ARITH (below).   *)
(* ------------------------------------------------------------------------- *)

let INT_OF_REAL_THM =
  let dest = `real_of_int`
  and real_ty = `:real`
  and int_ty = `:int`
  and cond_th = prove
   (`real_of_int(if b then x else y) =
       if b then real_of_int x else real_of_int y`,
    COND_CASES_TAC THEN REWRITE_TAC[]) in
  let thlist = map GSYM
   [int_eq; int_le; int_lt; int_ge; int_gt;
    int_of_num_th; int_neg_th; int_add_th; int_mul_th; int_sgn_th;
    int_sub_th; int_abs_th; int_max_th; int_min_th; int_pow_th; cond_th] in
  let REW_RULE = GEN_REWRITE_RULE DEPTH_CONV thlist in
  let int_tm_of_real_var v =
    let s,ty = dest_var v in
    if ty = real_ty then mk_comb(dest,mk_var(s,int_ty)) else v in
  let int_of_real_var v =
    let s,ty = dest_var v in
    if ty = real_ty then mk_var(s,int_ty) else v in
  let INT_OF_REAL_THM1 th =
    let newavs = subtract (frees (concl th)) (freesl (hyp th)) in
    let avs,bod = strip_forall(concl th) in
    let allavs = newavs@avs in
    let avs' = map int_tm_of_real_var allavs in
    let avs'' = map int_of_real_var avs in
    GENL avs'' (REW_RULE(SPECL avs' (GENL newavs th))) in
  let rec INT_OF_REAL_THM th =
    if is_conj(concl th) then CONJ (INT_OF_REAL_THM (CONJUNCT1 th))
                                   (INT_OF_REAL_THM (CONJUNCT2 th))
    else INT_OF_REAL_THM1 th in
  INT_OF_REAL_THM;;

(* ------------------------------------------------------------------------- *)
(* Collect together all the theorems derived automatically.                  *)
(* ------------------------------------------------------------------------- *)

let INT_ABS_0 = INT_OF_REAL_THM REAL_ABS_0;;
let INT_ABS_1 = INT_OF_REAL_THM REAL_ABS_1;;
let INT_ABS_ABS = INT_OF_REAL_THM REAL_ABS_ABS;;
let INT_ABS_BETWEEN = INT_OF_REAL_THM REAL_ABS_BETWEEN;;
let INT_ABS_BETWEEN1 = INT_OF_REAL_THM REAL_ABS_BETWEEN1;;
let INT_ABS_BETWEEN2 = INT_OF_REAL_THM REAL_ABS_BETWEEN2;;
let INT_ABS_BOUND = INT_OF_REAL_THM REAL_ABS_BOUND;;
let INT_ABS_BOUNDS = INT_OF_REAL_THM REAL_ABS_BOUNDS;;
let INT_ABS_CASES = INT_OF_REAL_THM REAL_ABS_CASES;;
let INT_ABS_CIRCLE = INT_OF_REAL_THM REAL_ABS_CIRCLE;;
let INT_ABS_LE = INT_OF_REAL_THM REAL_ABS_LE;;
let INT_ABS_MUL = INT_OF_REAL_THM REAL_ABS_MUL;;
let INT_ABS_NEG = INT_OF_REAL_THM REAL_ABS_NEG;;
let INT_ABS_NUM = INT_OF_REAL_THM REAL_ABS_NUM;;
let INT_ABS_NZ = INT_OF_REAL_THM REAL_ABS_NZ;;
let INT_ABS_POS = INT_OF_REAL_THM REAL_ABS_POS;;
let INT_ABS_POW = INT_OF_REAL_THM REAL_ABS_POW;;
let INT_ABS_REFL = INT_OF_REAL_THM REAL_ABS_REFL;;
let INT_ABS_SGN = INT_OF_REAL_THM REAL_ABS_SGN;;
let INT_ABS_SIGN = INT_OF_REAL_THM REAL_ABS_SIGN;;
let INT_ABS_SIGN2 = INT_OF_REAL_THM REAL_ABS_SIGN2;;
let INT_ABS_STILLNZ = INT_OF_REAL_THM REAL_ABS_STILLNZ;;
let INT_ABS_SUB = INT_OF_REAL_THM REAL_ABS_SUB;;
let INT_ABS_SUB_ABS = INT_OF_REAL_THM REAL_ABS_SUB_ABS;;
let INT_ABS_TRIANGLE = INT_OF_REAL_THM REAL_ABS_TRIANGLE;;
let INT_ABS_ZERO = INT_OF_REAL_THM REAL_ABS_ZERO;;
let INT_ADD2_SUB2 = INT_OF_REAL_THM REAL_ADD2_SUB2;;
let INT_ADD_AC = INT_OF_REAL_THM REAL_ADD_AC;;
let INT_ADD_ASSOC = INT_OF_REAL_THM REAL_ADD_ASSOC;;
let INT_ADD_LDISTRIB = INT_OF_REAL_THM REAL_ADD_LDISTRIB;;
let INT_ADD_LID = INT_OF_REAL_THM REAL_ADD_LID;;
let INT_ADD_LINV = INT_OF_REAL_THM REAL_ADD_LINV;;
let INT_ADD_RDISTRIB = INT_OF_REAL_THM REAL_ADD_RDISTRIB;;
let INT_ADD_RID = INT_OF_REAL_THM REAL_ADD_RID;;
let INT_ADD_RINV = INT_OF_REAL_THM REAL_ADD_RINV;;
let INT_ADD_SUB = INT_OF_REAL_THM REAL_ADD_SUB;;
let INT_ADD_SUB2 = INT_OF_REAL_THM REAL_ADD_SUB2;;
let INT_ADD_SYM = INT_OF_REAL_THM REAL_ADD_SYM;;
let INT_BOUNDS_LE = INT_OF_REAL_THM REAL_BOUNDS_LE;;
let INT_BOUNDS_LT = INT_OF_REAL_THM REAL_BOUNDS_LT;;
let INT_DIFFSQ = INT_OF_REAL_THM REAL_DIFFSQ;;
let INT_ENTIRE = INT_OF_REAL_THM REAL_ENTIRE;;
let INT_EQ_ADD_LCANCEL = INT_OF_REAL_THM REAL_EQ_ADD_LCANCEL;;
let INT_EQ_ADD_LCANCEL_0 = INT_OF_REAL_THM REAL_EQ_ADD_LCANCEL_0;;
let INT_EQ_ADD_RCANCEL = INT_OF_REAL_THM REAL_EQ_ADD_RCANCEL;;
let INT_EQ_ADD_RCANCEL_0 = INT_OF_REAL_THM REAL_EQ_ADD_RCANCEL_0;;
let INT_EQ_IMP_LE = INT_OF_REAL_THM REAL_EQ_IMP_LE;;
let INT_EQ_LCANCEL_IMP = INT_OF_REAL_THM REAL_EQ_LCANCEL_IMP;;
let INT_EQ_MUL_LCANCEL = INT_OF_REAL_THM REAL_EQ_MUL_LCANCEL;;
let INT_EQ_MUL_RCANCEL = INT_OF_REAL_THM REAL_EQ_MUL_RCANCEL;;
let INT_EQ_NEG2 = INT_OF_REAL_THM REAL_EQ_NEG2;;
let INT_EQ_RCANCEL_IMP = INT_OF_REAL_THM REAL_EQ_RCANCEL_IMP;;
let INT_EQ_SGN_ABS = INT_OF_REAL_THM REAL_EQ_SGN_ABS;;
let INT_EQ_SQUARE_ABS = INT_OF_REAL_THM REAL_EQ_SQUARE_ABS;;
let INT_EQ_SUB_LADD = INT_OF_REAL_THM REAL_EQ_SUB_LADD;;
let INT_EQ_SUB_RADD = INT_OF_REAL_THM REAL_EQ_SUB_RADD;;
let INT_EVENPOW_ABS = INT_OF_REAL_THM REAL_EVENPOW_ABS;;
let INT_LET_ADD = INT_OF_REAL_THM REAL_LET_ADD;;
let INT_LET_ADD2 = INT_OF_REAL_THM REAL_LET_ADD2;;
let INT_LET_ANTISYM = INT_OF_REAL_THM REAL_LET_ANTISYM;;
let INT_LET_TOTAL = INT_OF_REAL_THM REAL_LET_TOTAL;;
let INT_LET_TRANS = INT_OF_REAL_THM REAL_LET_TRANS;;
let INT_LE_01 = INT_OF_REAL_THM REAL_LE_01;;
let INT_LE_ADD = INT_OF_REAL_THM REAL_LE_ADD;;
let INT_LE_ADD2 = INT_OF_REAL_THM REAL_LE_ADD2;;
let INT_LE_ADDL = INT_OF_REAL_THM REAL_LE_ADDL;;
let INT_LE_ADDR = INT_OF_REAL_THM REAL_LE_ADDR;;
let INT_LE_ANTISYM = INT_OF_REAL_THM REAL_LE_ANTISYM;;
let INT_LE_DOUBLE = INT_OF_REAL_THM REAL_LE_DOUBLE;;
let INT_LE_LADD = INT_OF_REAL_THM REAL_LE_LADD;;
let INT_LE_LADD_IMP = INT_OF_REAL_THM REAL_LE_LADD_IMP;;
let INT_LE_LCANCEL_IMP = INT_OF_REAL_THM REAL_LE_LCANCEL_IMP;;
let INT_LE_LMUL = INT_OF_REAL_THM REAL_LE_LMUL;;
let INT_LE_LMUL_EQ = INT_OF_REAL_THM REAL_LE_LMUL_EQ;;
let INT_LE_LNEG = INT_OF_REAL_THM REAL_LE_LNEG;;
let INT_LE_LT = INT_OF_REAL_THM REAL_LE_LT;;
let INT_LE_MAX = INT_OF_REAL_THM REAL_LE_MAX;;
let INT_LE_MIN = INT_OF_REAL_THM REAL_LE_MIN;;
let INT_LE_MUL = INT_OF_REAL_THM REAL_LE_MUL;;
let INT_LE_MUL2 = INT_OF_REAL_THM REAL_LE_MUL2;;
let INT_LE_MUL_EQ = INT_OF_REAL_THM REAL_LE_MUL_EQ;;
let INT_LE_NEG2 = INT_OF_REAL_THM REAL_LE_NEG2;;
let INT_LE_NEGL = INT_OF_REAL_THM REAL_LE_NEGL;;
let INT_LE_NEGR = INT_OF_REAL_THM REAL_LE_NEGR;;
let INT_LE_NEGTOTAL = INT_OF_REAL_THM REAL_LE_NEGTOTAL;;
let INT_LE_POW2 = INT_OF_REAL_THM REAL_LE_POW2;;
let INT_LE_POW_2 = INT_OF_REAL_THM REAL_LE_POW_2;;
let INT_LE_RADD = INT_OF_REAL_THM REAL_LE_RADD;;
let INT_LE_RCANCEL_IMP = INT_OF_REAL_THM REAL_LE_RCANCEL_IMP;;
let INT_LE_REFL = INT_OF_REAL_THM REAL_LE_REFL;;
let INT_LE_RMUL = INT_OF_REAL_THM REAL_LE_RMUL;;
let INT_LE_RMUL_EQ = INT_OF_REAL_THM REAL_LE_RMUL_EQ;;
let INT_LE_RNEG = INT_OF_REAL_THM REAL_LE_RNEG;;
let INT_LE_SQUARE = INT_OF_REAL_THM REAL_LE_SQUARE;;
let INT_LE_SQUARE_ABS = INT_OF_REAL_THM REAL_LE_SQUARE_ABS;;
let INT_LE_SUB_LADD = INT_OF_REAL_THM REAL_LE_SUB_LADD;;
let INT_LE_SUB_RADD = INT_OF_REAL_THM REAL_LE_SUB_RADD;;
let INT_LE_TOTAL = INT_OF_REAL_THM REAL_LE_TOTAL;;
let INT_LE_TRANS = INT_OF_REAL_THM REAL_LE_TRANS;;
let INT_LNEG_UNIQ = INT_OF_REAL_THM REAL_LNEG_UNIQ;;
let INT_LTE_ADD = INT_OF_REAL_THM REAL_LTE_ADD;;
let INT_LTE_ADD2 = INT_OF_REAL_THM REAL_LTE_ADD2;;
let INT_LTE_ANTISYM = INT_OF_REAL_THM REAL_LTE_ANTISYM;;
let INT_LTE_TOTAL = INT_OF_REAL_THM REAL_LTE_TOTAL;;
let INT_LTE_TRANS = INT_OF_REAL_THM REAL_LTE_TRANS;;
let INT_LT_01 = INT_OF_REAL_THM REAL_LT_01;;
let INT_LT_ADD = INT_OF_REAL_THM REAL_LT_ADD;;
let INT_LT_ADD1 = INT_OF_REAL_THM REAL_LT_ADD1;;
let INT_LT_ADD2 = INT_OF_REAL_THM REAL_LT_ADD2;;
let INT_LT_ADDL = INT_OF_REAL_THM REAL_LT_ADDL;;
let INT_LT_ADDNEG = INT_OF_REAL_THM REAL_LT_ADDNEG;;
let INT_LT_ADDNEG2 = INT_OF_REAL_THM REAL_LT_ADDNEG2;;
let INT_LT_ADDR = INT_OF_REAL_THM REAL_LT_ADDR;;
let INT_LT_ADD_SUB = INT_OF_REAL_THM REAL_LT_ADD_SUB;;
let INT_LT_ANTISYM = INT_OF_REAL_THM REAL_LT_ANTISYM;;
let INT_LT_GT = INT_OF_REAL_THM REAL_LT_GT;;
let INT_LT_IMP_LE = INT_OF_REAL_THM REAL_LT_IMP_LE;;
let INT_LT_IMP_NE = INT_OF_REAL_THM REAL_LT_IMP_NE;;
let INT_LT_LADD = INT_OF_REAL_THM REAL_LT_LADD;;
let INT_LT_LADD_IMP = INT_OF_REAL_THM REAL_LT_LADD_IMP;;
let INT_LT_LCANCEL_IMP = INT_OF_REAL_THM REAL_LT_LCANCEL_IMP;;
let INT_LT_LE = INT_OF_REAL_THM REAL_LT_LE;;
let INT_LT_LMUL = INT_OF_REAL_THM REAL_LT_LMUL;;
let INT_LT_LMUL_EQ = INT_OF_REAL_THM REAL_LT_LMUL_EQ;;
let INT_LT_LNEG = INT_OF_REAL_THM REAL_LT_LNEG;;
let INT_LT_MAX = INT_OF_REAL_THM REAL_LT_MAX;;
let INT_LT_MIN = INT_OF_REAL_THM REAL_LT_MIN;;
let INT_LT_MUL = INT_OF_REAL_THM REAL_LT_MUL;;
let INT_LT_MUL2 = INT_OF_REAL_THM REAL_LT_MUL2;;
let INT_LT_MUL_EQ = INT_OF_REAL_THM REAL_LT_MUL_EQ;;
let INT_LT_NEG2 = INT_OF_REAL_THM REAL_LT_NEG2;;
let INT_LT_NEGTOTAL = INT_OF_REAL_THM REAL_LT_NEGTOTAL;;
let INT_LT_POW2 = INT_OF_REAL_THM REAL_LT_POW2;;
let INT_LT_POW_2 = INT_OF_REAL_THM REAL_LT_POW_2;;
let INT_LT_RADD = INT_OF_REAL_THM REAL_LT_RADD;;
let INT_LT_RCANCEL_IMP = INT_OF_REAL_THM REAL_LT_RCANCEL_IMP;;
let INT_LT_REFL = INT_OF_REAL_THM REAL_LT_REFL;;
let INT_LT_RMUL = INT_OF_REAL_THM REAL_LT_RMUL;;
let INT_LT_RMUL_EQ = INT_OF_REAL_THM REAL_LT_RMUL_EQ;;
let INT_LT_RNEG = INT_OF_REAL_THM REAL_LT_RNEG;;
let INT_LT_SQUARE = INT_OF_REAL_THM REAL_LT_SQUARE;;
let INT_LT_SQUARE_ABS = INT_OF_REAL_THM REAL_LT_SQUARE_ABS;;
let INT_LT_SUB_LADD = INT_OF_REAL_THM REAL_LT_SUB_LADD;;
let INT_LT_SUB_RADD = INT_OF_REAL_THM REAL_LT_SUB_RADD;;
let INT_LT_TOTAL = INT_OF_REAL_THM REAL_LT_TOTAL;;
let INT_LT_TRANS = INT_OF_REAL_THM REAL_LT_TRANS;;
let INT_MAX_ACI = INT_OF_REAL_THM REAL_MAX_ACI;;
let INT_MAX_ASSOC = INT_OF_REAL_THM REAL_MAX_ASSOC;;
let INT_MAX_LE = INT_OF_REAL_THM REAL_MAX_LE;;
let INT_MAX_LT = INT_OF_REAL_THM REAL_MAX_LT;;
let INT_MAX_MAX = INT_OF_REAL_THM REAL_MAX_MAX;;
let INT_MAX_MIN = INT_OF_REAL_THM REAL_MAX_MIN;;
let INT_MAX_SYM = INT_OF_REAL_THM REAL_MAX_SYM;;
let INT_MIN_ACI = INT_OF_REAL_THM REAL_MIN_ACI;;
let INT_MIN_ASSOC = INT_OF_REAL_THM REAL_MIN_ASSOC;;
let INT_MIN_LE = INT_OF_REAL_THM REAL_MIN_LE;;
let INT_MIN_LT = INT_OF_REAL_THM REAL_MIN_LT;;
let INT_MIN_MAX = INT_OF_REAL_THM REAL_MIN_MAX;;
let INT_MIN_MIN = INT_OF_REAL_THM REAL_MIN_MIN;;
let INT_MIN_SYM = INT_OF_REAL_THM REAL_MIN_SYM;;
let INT_MUL_2 = INT_OF_REAL_THM REAL_MUL_2;;
let INT_MUL_AC = INT_OF_REAL_THM REAL_MUL_AC;;
let INT_MUL_ASSOC = INT_OF_REAL_THM REAL_MUL_ASSOC;;
let INT_MUL_LID = INT_OF_REAL_THM REAL_MUL_LID;;
let INT_MUL_LNEG = INT_OF_REAL_THM REAL_MUL_LNEG;;
let INT_MUL_LZERO = INT_OF_REAL_THM REAL_MUL_LZERO;;
let INT_MUL_POS_LE = INT_OF_REAL_THM REAL_MUL_POS_LE;;
let INT_MUL_POS_LT = INT_OF_REAL_THM REAL_MUL_POS_LT;;
let INT_MUL_RID = INT_OF_REAL_THM REAL_MUL_RID;;
let INT_MUL_RNEG = INT_OF_REAL_THM REAL_MUL_RNEG;;
let INT_MUL_RZERO = INT_OF_REAL_THM REAL_MUL_RZERO;;
let INT_MUL_SYM = INT_OF_REAL_THM REAL_MUL_SYM;;
let INT_NEG_0 = INT_OF_REAL_THM REAL_NEG_0;;
let INT_NEG_ADD = INT_OF_REAL_THM REAL_NEG_ADD;;
let INT_NEG_EQ = INT_OF_REAL_THM REAL_NEG_EQ;;
let INT_NEG_EQ_0 = INT_OF_REAL_THM REAL_NEG_EQ_0;;
let INT_NEG_GE0 = INT_OF_REAL_THM REAL_NEG_GE0;;
let INT_NEG_GT0 = INT_OF_REAL_THM REAL_NEG_GT0;;
let INT_NEG_LE0 = INT_OF_REAL_THM REAL_NEG_LE0;;
let INT_NEG_LMUL = INT_OF_REAL_THM REAL_NEG_LMUL;;
let INT_NEG_LT0 = INT_OF_REAL_THM REAL_NEG_LT0;;
let INT_NEG_MINUS1 = INT_OF_REAL_THM REAL_NEG_MINUS1;;
let INT_NEG_MUL2 = INT_OF_REAL_THM REAL_NEG_MUL2;;
let INT_NEG_NEG = INT_OF_REAL_THM REAL_NEG_NEG;;
let INT_NEG_RMUL = INT_OF_REAL_THM REAL_NEG_RMUL;;
let INT_NEG_SUB = INT_OF_REAL_THM REAL_NEG_SUB;;
let INT_NOT_EQ = INT_OF_REAL_THM REAL_NOT_EQ;;
let INT_NOT_LE = INT_OF_REAL_THM REAL_NOT_LE;;
let INT_NOT_LT = INT_OF_REAL_THM REAL_NOT_LT;;
let INT_OF_NUM_ADD = INT_OF_REAL_THM REAL_OF_NUM_ADD;;
let INT_OF_NUM_CLAUSES = INT_OF_REAL_THM REAL_OF_NUM_CLAUSES;;
let INT_OF_NUM_EQ = INT_OF_REAL_THM REAL_OF_NUM_EQ;;
let INT_OF_NUM_GE = INT_OF_REAL_THM REAL_OF_NUM_GE;;
let INT_OF_NUM_GT = INT_OF_REAL_THM REAL_OF_NUM_GT;;
let INT_OF_NUM_LE = INT_OF_REAL_THM REAL_OF_NUM_LE;;
let INT_OF_NUM_LT = INT_OF_REAL_THM REAL_OF_NUM_LT;;
let INT_OF_NUM_MAX = INT_OF_REAL_THM REAL_OF_NUM_MAX;;
let INT_OF_NUM_MIN = INT_OF_REAL_THM REAL_OF_NUM_MIN;;
let INT_OF_NUM_MOD = INT_OF_REAL_THM REAL_OF_NUM_MOD;;
let INT_OF_NUM_MUL = INT_OF_REAL_THM REAL_OF_NUM_MUL;;
let INT_OF_NUM_POW = INT_OF_REAL_THM REAL_OF_NUM_POW;;
let INT_OF_NUM_SUB = INT_OF_REAL_THM REAL_OF_NUM_SUB;;
let INT_OF_NUM_SUB_CASES = INT_OF_REAL_THM REAL_OF_NUM_SUB_CASES;;
let INT_OF_NUM_SUC = INT_OF_REAL_THM REAL_OF_NUM_SUC;;
let INT_POS = INT_OF_REAL_THM REAL_POS;;
let INT_POS_EQ_SQUARE = INT_OF_REAL_THM REAL_POS_EQ_SQUARE;;
let INT_POS_NZ = INT_OF_REAL_THM REAL_LT_IMP_NZ;;
let INT_POW2_ABS = INT_OF_REAL_THM REAL_POW2_ABS;;
let INT_POW_1 = INT_OF_REAL_THM REAL_POW_1;;
let INT_POW_1_LE = INT_OF_REAL_THM REAL_POW_1_LE;;
let INT_POW_1_LT = INT_OF_REAL_THM REAL_POW_1_LT;;
let INT_POW_2 = INT_OF_REAL_THM REAL_POW_2;;
let INT_POW_ADD = INT_OF_REAL_THM REAL_POW_ADD;;
let INT_POW_EQ = INT_OF_REAL_THM REAL_POW_EQ;;
let INT_POW_EQ_0 = INT_OF_REAL_THM REAL_POW_EQ_0;;
let INT_POW_EQ_1 = INT_OF_REAL_THM REAL_POW_EQ_1;;
let INT_POW_EQ_1_IMP = INT_OF_REAL_THM REAL_POW_EQ_1_IMP;;
let INT_POW_EQ_ABS = INT_OF_REAL_THM REAL_POW_EQ_ABS;;
let INT_POW_EQ_EQ = INT_OF_REAL_THM REAL_POW_EQ_EQ;;
let INT_POW_EQ_ODD = INT_OF_REAL_THM REAL_POW_EQ_ODD;;
let INT_POW_EQ_ODD_EQ = INT_OF_REAL_THM REAL_POW_EQ_ODD_EQ;;
let INT_POW_LBOUND = INT_OF_REAL_THM REAL_POW_LBOUND;;
let INT_POW_LE = INT_OF_REAL_THM REAL_POW_LE;;
let INT_POW_LE2 = INT_OF_REAL_THM REAL_POW_LE2;;
let INT_POW_LE2_ODD = INT_OF_REAL_THM REAL_POW_LE2_ODD;;
let INT_POW_LE2_ODD_EQ = INT_OF_REAL_THM REAL_POW_LE2_ODD_EQ;;
let INT_POW_LE2_REV = INT_OF_REAL_THM REAL_POW_LE2_REV;;
let INT_POW_LE_1 = INT_OF_REAL_THM REAL_POW_LE_1;;
let INT_POW_LT = INT_OF_REAL_THM REAL_POW_LT;;
let INT_POW_LT2 = INT_OF_REAL_THM REAL_POW_LT2;;
let INT_POW_LT2_ODD = INT_OF_REAL_THM REAL_POW_LT2_ODD;;
let INT_POW_LT2_ODD_EQ = INT_OF_REAL_THM REAL_POW_LT2_ODD_EQ;;
let INT_POW_LT2_REV = INT_OF_REAL_THM REAL_POW_LT2_REV;;
let INT_POW_LT_1 = INT_OF_REAL_THM REAL_POW_LT_1;;
let INT_POW_MONO = INT_OF_REAL_THM REAL_POW_MONO;;
let INT_POW_MONO_LT = INT_OF_REAL_THM REAL_POW_MONO_LT;;
let INT_POW_MUL = INT_OF_REAL_THM REAL_POW_MUL;;
let INT_POW_NEG = INT_OF_REAL_THM REAL_POW_NEG;;
let INT_POW_NZ = INT_OF_REAL_THM REAL_POW_NZ;;
let INT_POW_ONE = INT_OF_REAL_THM REAL_POW_ONE;;
let INT_POW_POW = INT_OF_REAL_THM REAL_POW_POW;;
let INT_POW_ZERO = INT_OF_REAL_THM REAL_POW_ZERO;;
let INT_RNEG_UNIQ = INT_OF_REAL_THM REAL_RNEG_UNIQ;;
let INT_SGN = INT_OF_REAL_THM real_sgn;;
let INT_SGNS_EQ = INT_OF_REAL_THM REAL_SGNS_EQ;;
let INT_SGNS_EQ_ALT = INT_OF_REAL_THM REAL_SGNS_EQ_ALT;;
let INT_SGN_0 = INT_OF_REAL_THM REAL_SGN_0;;
let INT_SGN_ABS = INT_OF_REAL_THM REAL_SGN_ABS;;
let INT_SGN_ABS_ALT = INT_OF_REAL_THM REAL_SGN_ABS_ALT;;
let INT_SGN_CASES = INT_OF_REAL_THM REAL_SGN_CASES;;
let INT_SGN_EQ = INT_OF_REAL_THM REAL_SGN_EQ;;
let INT_SGN_EQ_INEQ = INT_OF_REAL_THM REAL_SGN_EQ_INEQ;;
let INT_SGN_INEQS = INT_OF_REAL_THM REAL_SGN_INEQS;;
let INT_SGN_INT_SGN = INT_OF_REAL_THM REAL_SGN_REAL_SGN;;
let INT_SGN_MUL = INT_OF_REAL_THM REAL_SGN_MUL;;
let INT_SGN_NEG = INT_OF_REAL_THM REAL_SGN_NEG;;
let INT_SGN_POW = INT_OF_REAL_THM REAL_SGN_POW;;
let INT_SGN_POW_2 = INT_OF_REAL_THM REAL_SGN_POW_2;;
let INT_SOS_EQ_0 = INT_OF_REAL_THM REAL_SOS_EQ_0;;
let INT_SUB_0 = INT_OF_REAL_THM REAL_SUB_0;;
let INT_SUB_ABS = INT_OF_REAL_THM REAL_SUB_ABS;;
let INT_SUB_ADD = INT_OF_REAL_THM REAL_SUB_ADD;;
let INT_SUB_ADD2 = INT_OF_REAL_THM REAL_SUB_ADD2;;
let INT_SUB_LDISTRIB = INT_OF_REAL_THM REAL_SUB_LDISTRIB;;
let INT_SUB_LE = INT_OF_REAL_THM REAL_SUB_LE;;
let INT_SUB_LNEG = INT_OF_REAL_THM REAL_SUB_LNEG;;
let INT_SUB_LT = INT_OF_REAL_THM REAL_SUB_LT;;
let INT_SUB_LZERO = INT_OF_REAL_THM REAL_SUB_LZERO;;
let INT_SUB_NEG2 = INT_OF_REAL_THM REAL_SUB_NEG2;;
let INT_SUB_RDISTRIB = INT_OF_REAL_THM REAL_SUB_RDISTRIB;;
let INT_SUB_REFL = INT_OF_REAL_THM REAL_SUB_REFL;;
let INT_SUB_RNEG = INT_OF_REAL_THM REAL_SUB_RNEG;;
let INT_SUB_RZERO = INT_OF_REAL_THM REAL_SUB_RZERO;;
let INT_SUB_SUB = INT_OF_REAL_THM REAL_SUB_SUB;;
let INT_SUB_SUB2 = INT_OF_REAL_THM REAL_SUB_SUB2;;
let INT_SUB_TRIANGLE = INT_OF_REAL_THM REAL_SUB_TRIANGLE;;

let INT_WLOG_LE = prove
 (`(!x y:int. P x y <=> P y x) /\ (!x y. x <= y ==> P x y) ==> !x y. P x y`,
  MESON_TAC[INT_LE_TOTAL]);;

let INT_WLOG_LT = prove
 (`(!x:int. P x x) /\ (!x y. P x y <=> P y x) /\ (!x y. x < y ==> P x y)
   ==> !x y. P x y`,
  MESON_TAC[INT_LT_TOTAL]);;

let INT_WLOG_LE_3 = prove
 (`!P. (!x y z. P x y z ==> P y x z /\ P x z y) /\
       (!x y z:int. x <= y /\ y <= z ==> P x y z)
       ==> !x y z. P x y z`,
  MESON_TAC[INT_LE_TOTAL]);;

(* ------------------------------------------------------------------------- *)
(* More useful "image" theorems.                                             *)
(* ------------------------------------------------------------------------- *)

let INT_FORALL_POS = prove
 (`!P. (!n. P(&n)) <=> (!i:int. &0 <= i ==> P(i))`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN GEN_TAC THENL
   [DISJ_CASES_THEN (CHOOSE_THEN SUBST1_TAC) (SPEC `i:int` INT_IMAGE) THEN
    ASM_REWRITE_TAC[INT_LE_RNEG; INT_ADD_LID; INT_OF_NUM_LE; LE] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[INT_NEG_0];
    FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[INT_OF_NUM_LE; LE_0]]);;

let INT_EXISTS_POS = prove
 (`!P. (?n. P(&n)) <=> (?i:int. &0 <= i /\ P(i))`,
  GEN_TAC THEN GEN_REWRITE_TAC I [TAUT `(p <=> q) <=> (~p <=> ~q)`] THEN
  REWRITE_TAC[NOT_EXISTS_THM; INT_FORALL_POS] THEN MESON_TAC[]);;

let INT_FORALL_ABS = prove
 (`!P. (!n. P(&n)) <=> (!x:int. P(abs x))`,
  REWRITE_TAC[INT_FORALL_POS] THEN MESON_TAC[INT_ABS_POS; INT_ABS_REFL]);;

let INT_EXISTS_ABS = prove
 (`!P. (?n. P(&n)) <=> (?x:int. P(abs x))`,
  GEN_TAC THEN GEN_REWRITE_TAC I [TAUT `(p <=> q) <=> (~p <=> ~q)`] THEN
  REWRITE_TAC[NOT_EXISTS_THM; INT_FORALL_ABS] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A few "pseudo definitions".                                               *)
(* ------------------------------------------------------------------------- *)

let INT_POW = prove
 (`(x pow 0 = &1) /\
   (!n. x pow (SUC n) = x * x pow n)`,
  REWRITE_TAC(map INT_OF_REAL_THM (CONJUNCTS real_pow)));;

let INT_ABS = prove
 (`!x. abs(x) = if &0 <= x then x else --x`,
  GEN_TAC THEN MP_TAC(INT_OF_REAL_THM(SPEC `x:real` real_abs)) THEN
  COND_CASES_TAC THEN REWRITE_TAC[int_eq]);;

let INT_GE = prove
 (`!x y. x >= y <=> y <= x`,
  REWRITE_TAC[int_ge; int_le; real_ge]);;

let INT_GT = prove
 (`!x y. x > y <=> y < x`,
  REWRITE_TAC[int_gt; int_lt; real_gt]);;

let INT_LT = prove
 (`!x y. x < y <=> ~(y <= x)`,
  REWRITE_TAC[int_lt; int_le; real_lt]);;

(* ------------------------------------------------------------------------- *)
(* An initial bootstrapping procedure for the integers, enhanced later.      *)
(* ------------------------------------------------------------------------- *)

let INT_ARITH =
  let atom_CONV =
    let pth = prove
      (`(~(x:int <= y) <=> y + &1 <= x) /\
        (~(x < y) <=> y <= x) /\
        (~(x = y) <=> x + &1 <= y \/ y + &1 <= x) /\
        (x < y <=> x + &1 <= y)`,
       REWRITE_TAC[INT_NOT_LE; INT_NOT_LT; INT_NOT_EQ; INT_LT_DISCRETE]) in
    GEN_REWRITE_CONV I [pth]
  and bub_CONV = GEN_REWRITE_CONV TOP_SWEEP_CONV
   [int_eq; int_le; int_lt; int_ge; int_gt;
    int_of_num_th; int_neg_th; int_add_th; int_mul_th;
    int_sub_th; int_pow_th; int_abs_th; int_max_th; int_min_th] in
  let base_CONV = TRY_CONV atom_CONV THENC bub_CONV in
  let NNF_NORM_CONV = GEN_NNF_CONV false
   (base_CONV,fun t -> base_CONV t,base_CONV(mk_neg t)) in
  let init_CONV =
    TOP_DEPTH_CONV BETA_CONV THENC
    PRESIMP_CONV THENC
    GEN_REWRITE_CONV DEPTH_CONV [INT_GT; INT_GE] THENC
    NNF_CONV THENC DEPTH_BINOP_CONV `(\/)` CONDS_ELIM_CONV THENC
    NNF_NORM_CONV in
  let p_tm = `p:bool`
  and not_tm = `(~)` in
  let pth = TAUT(mk_eq(mk_neg(mk_neg p_tm),p_tm)) in
  fun tm ->
    let th0 = INST [tm,p_tm] pth
    and th1 = init_CONV (mk_neg tm) in
    let th2 = REAL_ARITH(mk_neg(rand(concl th1))) in
    EQ_MP th0 (EQ_MP (AP_TERM not_tm (SYM th1)) th2);;

let INT_ARITH_TAC = CONV_TAC(EQT_INTRO o INT_ARITH);;

let ASM_INT_ARITH_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (not o is_forall o concl))) THEN
  INT_ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* Some pseudo-definitions.                                                  *)
(* ------------------------------------------------------------------------- *)

let INT_SUB = INT_ARITH `!x y. x - y = x + --y`;;

let INT_MAX = INT_ARITH `!x y. max x y = if x <= y then y else x`;;

let INT_MIN = INT_ARITH `!x y. min x y = if x <= y then x else y`;;

(* ------------------------------------------------------------------------- *)
(* Additional useful lemmas.                                                 *)
(* ------------------------------------------------------------------------- *)

let INT_OF_NUM_EXISTS = prove
 (`!x:int. (?n. x = &n) <=> &0 <= x`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[INT_POS] THEN
  MP_TAC(ISPEC `x:int` INT_IMAGE) THEN
  REWRITE_TAC[OR_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_INT_ARITH_TAC);;

let INT_LE_DISCRETE = INT_ARITH `!x y:int. x <= y <=> x < y + &1`;;

let INT_LE_TRANS_LE = prove
 (`!x y:int. x <= y <=> (!z. y <= z ==> x <= z)`,
  MESON_TAC[INT_LE_TRANS; INT_LE_REFL]);;

let INT_LE_TRANS_LT = prove
 (`!x y:int. x <= y <=> (!z. y < z ==> x < z)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y + &1:int`) THEN INT_ARITH_TAC);;

let INT_MUL_EQ_1 = prove
 (`!x y:int. x * y = &1 <=> x = &1 /\ y = &1 \/ x = --(&1) /\ y = --(&1)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `x:int` INT_IMAGE) THEN
  MP_TAC(ISPEC `y:int` INT_IMAGE) THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[INT_MUL_LNEG; INT_MUL_RNEG; INT_NEG_NEG;
     INT_ARITH `~(--(&n:int) = &1)`; INT_OF_NUM_MUL;
     INT_ARITH `~(&n:int = -- &1)`; INT_OF_NUM_EQ; INT_NEG_EQ] THEN
  REWRITE_TAC[MULT_EQ_1]);;

let INT_ABS_MUL_1 = prove
 (`!x y. abs(x * y) = &1 <=> abs(x) = &1 /\ abs(y) = &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_ABS_MUL] THEN
  MP_TAC(SPEC `y:int` INT_ABS_POS) THEN SPEC_TAC(`abs(y)`,`b:int`) THEN
  MP_TAC(SPEC `x:int` INT_ABS_POS) THEN SPEC_TAC(`abs(x)`,`a:int`) THEN
  REWRITE_TAC[GSYM INT_FORALL_POS; INT_OF_NUM_MUL; INT_OF_NUM_EQ; MULT_EQ_1]);;

let INT_WOP = prove
 (`(?x. &0 <= x /\ P x) <=>
   (?x. &0 <= x /\ P x /\ !y. &0 <= y /\ P y ==> x <= y)`,
  ONCE_REWRITE_TAC[MESON[] `(?x. P x /\ Q x) <=> ~(!x. P x ==> ~Q x)`] THEN
  REWRITE_TAC[IMP_CONJ; GSYM INT_FORALL_POS; INT_OF_NUM_LE] THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  REWRITE_TAC[GSYM NOT_LE; CONTRAPOS_THM]);;

(* ------------------------------------------------------------------------- *)
(* Archimedian property for the integers.                                    *)
(* ------------------------------------------------------------------------- *)

let INT_ARCH = prove
 (`!x d. ~(d = &0) ==> ?c. x < c * d`,
  SUBGOAL_THEN `!x. &0 <= x ==> ?n. x <= &n` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_FORALL_POS; INT_OF_NUM_LE] THEN MESON_TAC[LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. ?n. x <= &n` ASSUME_TAC THENL
   [ASM_MESON_TAC[INT_LE_TOTAL]; ALL_TAC] THEN
  SUBGOAL_THEN `!x d. &0 < d ==> ?c. x < c * d` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[INT_LT_DISCRETE; INT_ADD_LID] THEN
    ASM_MESON_TAC[INT_POS; INT_LE_LMUL; INT_ARITH
        `x + &1 <= &n /\ &n * &1 <= &n * d ==> x + &1 <= &n * d`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x d. ~(d = &0) ==> ?c. x < c * d` ASSUME_TAC THENL
   [ASM_MESON_TAC[INT_ARITH `--x * y = x * --y`;
                  INT_ARITH `~(d = &0) ==> &0 < d \/ &0 < --d`];
    ALL_TAC] THEN
  ASM_MESON_TAC[INT_ARITH `--x * y = x * --y`;
                INT_ARITH `~(d = &0) ==> &0 < d \/ &0 < --d`]);;

(* ------------------------------------------------------------------------- *)
(* Definitions of ("Euclidean") integer division and remainder.              *)
(* ------------------------------------------------------------------------- *)

let INT_DIVMOD_EXIST_0 = prove
 (`!m n:int. ?q r. if n = &0 then q = &0 /\ r = m
                   else &0 <= r /\ r < abs(n) /\ m = q * n + r`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = &0` THEN
  ASM_REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_REFL] THEN
  GEN_REWRITE_TAC I [SWAP_EXISTS_THM] THEN
  SUBGOAL_THEN `?r. &0 <= r /\ ?q:int. m = n * q + r` MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `--m:int` o MATCH_MP INT_ARCH) THEN
    DISCH_THEN(X_CHOOSE_TAC `s:int`) THEN
    EXISTS_TAC `m + s * n:int` THEN CONJ_TAC THENL
     [ASM_INT_ARITH_TAC; EXISTS_TAC `--s:int` THEN INT_ARITH_TAC];
    GEN_REWRITE_TAC LAND_CONV [INT_WOP] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:int` THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:int` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `r - abs n`) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `if &0 <= n then q + &1 else q - &1`) THEN
    ASM_INT_ARITH_TAC]);;

parse_as_infix("div",(22,"left"));;
parse_as_infix("rem",(22,"left"));;

let INT_DIVISION_0 =  new_specification ["div"; "rem"]
  (REWRITE_RULE[SKOLEM_THM] INT_DIVMOD_EXIST_0);;

let INT_DIVISION = prove
 (`!m n. ~(n = &0)
         ==> m = m div n * n + m rem n /\ &0 <= m rem n /\ m rem n < abs n`,
  MESON_TAC[INT_DIVISION_0]);;

let INT_DIVISION_SIMP = prove
 (`!m n. m div n * n + m rem n = m`,
  MP_TAC INT_DIVISION_0 THEN REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN CONV_TAC INT_ARITH);;

let INT_REM_POS = prove
 (`!a b. ~(b = &0) ==> &0 <= a rem b`,
  MESON_TAC[INT_DIVISION]);;

let INT_DIV_0 = prove
 (`!m. m div &0 = &0`,
  MESON_TAC[INT_DIVISION_0]);;

let INT_REM_0 = prove
 (`!m. m rem &0 = m`,
  MESON_TAC[INT_DIVISION_0]);;

let INT_REM_POS_EQ = prove
 (`!m n. &0 <= m rem n <=> n = &0 ==> &0 <= m`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n:int = &0` THEN
  ASM_SIMP_TAC[INT_REM_0; INT_REM_POS]);;

let INT_REM_DIV = prove
 (`!m n. m rem n = m - m div n * n`,
  REWRITE_TAC[INT_ARITH `a:int = b - c <=> c + a = b`] THEN
  REWRITE_TAC[INT_DIVISION_SIMP]);;

let INT_LT_REM = prove
 (`!x n. &0 < n ==> x rem n < n`,
  MESON_TAC[INT_DIVISION; INT_LT_REFL; INT_ARITH `&0:int < n ==> abs n = n`]);;

let INT_LT_REM_EQ = prove
 (`!m n. m rem n < n <=> &0 < n \/ n = &0 /\ m < &0`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n:int = &0` THEN
  ASM_SIMP_TAC[INT_REM_0; INT_LT_REFL] THEN
  EQ_TAC THEN REWRITE_TAC[INT_LT_REM] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] INT_LET_TRANS) THEN
  ASM_SIMP_TAC[INT_REM_POS]);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic operations on integers. Essentially a clone of stuff for reals *)
(* in the file "calc_int.ml", except for div and rem, which are more like N. *)
(* ------------------------------------------------------------------------- *)

let INT_LE_CONV,INT_LT_CONV,INT_GE_CONV,INT_GT_CONV,INT_EQ_CONV =
  let tth =
    TAUT `(F /\ F <=> F) /\ (F /\ T <=> F) /\
          (T /\ F <=> F) /\ (T /\ T <=> T)` in
  let nth = TAUT `(~T <=> F) /\ (~F <=> T)` in
  let NUM2_EQ_CONV = BINOP_CONV NUM_EQ_CONV THENC GEN_REWRITE_CONV I [tth] in
  let NUM2_NE_CONV =
    RAND_CONV NUM2_EQ_CONV THENC
    GEN_REWRITE_CONV I [nth] in
  let [pth_le1; pth_le2a; pth_le2b; pth_le3] = (CONJUNCTS o prove)
   (`(--(&m) <= &n <=> T) /\
     (&m <= &n <=> m <= n) /\
     (--(&m) <= --(&n) <=> n <= m) /\
     (&m <= --(&n) <=> (m = 0) /\ (n = 0))`,
    REWRITE_TAC[INT_LE_NEG2] THEN
    REWRITE_TAC[INT_LE_LNEG; INT_LE_RNEG] THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_LE; LE_0] THEN
    REWRITE_TAC[LE; ADD_EQ_0]) in
  let INT_LE_CONV = FIRST_CONV
   [GEN_REWRITE_CONV I [pth_le1];
    GEN_REWRITE_CONV I [pth_le2a; pth_le2b] THENC NUM_LE_CONV;
    GEN_REWRITE_CONV I [pth_le3] THENC NUM2_EQ_CONV] in
  let [pth_lt1; pth_lt2a; pth_lt2b; pth_lt3] = (CONJUNCTS o prove)
   (`(&m < --(&n) <=> F) /\
     (&m < &n <=> m < n) /\
     (--(&m) < --(&n) <=> n < m) /\
     (--(&m) < &n <=> ~((m = 0) /\ (n = 0)))`,
    REWRITE_TAC[pth_le1; pth_le2a; pth_le2b; pth_le3;
                GSYM NOT_LE; INT_LT] THEN
    CONV_TAC TAUT) in
  let INT_LT_CONV = FIRST_CONV
   [GEN_REWRITE_CONV I [pth_lt1];
    GEN_REWRITE_CONV I [pth_lt2a; pth_lt2b] THENC NUM_LT_CONV;
    GEN_REWRITE_CONV I [pth_lt3] THENC NUM2_NE_CONV] in
  let [pth_ge1; pth_ge2a; pth_ge2b; pth_ge3] = (CONJUNCTS o prove)
   (`(&m >= --(&n) <=> T) /\
     (&m >= &n <=> n <= m) /\
     (--(&m) >= --(&n) <=> m <= n) /\
     (--(&m) >= &n <=> (m = 0) /\ (n = 0))`,
    REWRITE_TAC[pth_le1; pth_le2a; pth_le2b; pth_le3; INT_GE] THEN
    CONV_TAC TAUT) in
  let INT_GE_CONV = FIRST_CONV
   [GEN_REWRITE_CONV I [pth_ge1];
    GEN_REWRITE_CONV I [pth_ge2a; pth_ge2b] THENC NUM_LE_CONV;
    GEN_REWRITE_CONV I [pth_ge3] THENC NUM2_EQ_CONV] in
  let [pth_gt1; pth_gt2a; pth_gt2b; pth_gt3] = (CONJUNCTS o prove)
   (`(--(&m) > &n <=> F) /\
     (&m > &n <=> n < m) /\
     (--(&m) > --(&n) <=> m < n) /\
     (&m > --(&n) <=> ~((m = 0) /\ (n = 0)))`,
    REWRITE_TAC[pth_lt1; pth_lt2a; pth_lt2b; pth_lt3; INT_GT] THEN
    CONV_TAC TAUT) in
  let INT_GT_CONV = FIRST_CONV
   [GEN_REWRITE_CONV I [pth_gt1];
    GEN_REWRITE_CONV I [pth_gt2a; pth_gt2b] THENC NUM_LT_CONV;
    GEN_REWRITE_CONV I [pth_gt3] THENC NUM2_NE_CONV] in
  let [pth_eq1a; pth_eq1b; pth_eq2a; pth_eq2b] = (CONJUNCTS o prove)
   (`((&m = &n) <=> (m = n)) /\
     ((--(&m) = --(&n)) <=> (m = n)) /\
     ((--(&m) = &n) <=> (m = 0) /\ (n = 0)) /\
     ((&m = --(&n)) <=> (m = 0) /\ (n = 0))`,
    REWRITE_TAC[GSYM INT_LE_ANTISYM; GSYM LE_ANTISYM] THEN
    REWRITE_TAC[pth_le1; pth_le2a; pth_le2b; pth_le3; LE; LE_0] THEN
    CONV_TAC TAUT) in
  let INT_EQ_CONV = FIRST_CONV
   [GEN_REWRITE_CONV I [pth_eq1a; pth_eq1b] THENC NUM_EQ_CONV;
    GEN_REWRITE_CONV I [pth_eq2a; pth_eq2b] THENC NUM2_EQ_CONV] in
  INT_LE_CONV,INT_LT_CONV,
  INT_GE_CONV,INT_GT_CONV,INT_EQ_CONV;;

let INT_NEG_CONV =
  let pth = prove
   (`(--(&0) = &0) /\
     (--(--(&x)) = &x)`,
    REWRITE_TAC[INT_NEG_NEG; INT_NEG_0]) in
  GEN_REWRITE_CONV I [pth];;

let INT_MUL_CONV =
  let pth0 = prove
   (`(&0 * &x = &0) /\
     (&0 * --(&x) = &0) /\
     (&x * &0 = &0) /\
     (--(&x) * &0 = &0)`,
    REWRITE_TAC[INT_MUL_LZERO; INT_MUL_RZERO])
  and pth1,pth2 = (CONJ_PAIR o prove)
   (`((&m * &n = &(m * n)) /\
      (--(&m) * --(&n) = &(m * n))) /\
     ((--(&m) * &n = --(&(m * n))) /\
      (&m * --(&n) = --(&(m * n))))`,
    REWRITE_TAC[INT_MUL_LNEG; INT_MUL_RNEG; INT_NEG_NEG] THEN
    REWRITE_TAC[INT_OF_NUM_MUL]) in
  FIRST_CONV
   [GEN_REWRITE_CONV I [pth0];
    GEN_REWRITE_CONV I [pth1] THENC RAND_CONV NUM_MULT_CONV;
    GEN_REWRITE_CONV I [pth2] THENC RAND_CONV(RAND_CONV NUM_MULT_CONV)];;

let INT_ADD_CONV =
  let neg_tm = `(--)` in
  let amp_tm = `&` in
  let add_tm = `(+)` in
  let dest = dest_binop `(+)` in
  let m_tm = `m:num` and n_tm = `n:num` in
  let pth0 = prove
   (`(--(&m) + &m = &0) /\
     (&m + --(&m) = &0)`,
    REWRITE_TAC[INT_ADD_LINV; INT_ADD_RINV]) in
  let [pth1; pth2; pth3; pth4; pth5; pth6] = (CONJUNCTS o prove)
   (`(--(&m) + --(&n) = --(&(m + n))) /\
     (--(&m) + &(m + n) = &n) /\
     (--(&(m + n)) + &m = --(&n)) /\
     (&(m + n) + --(&m) = &n) /\
     (&m + --(&(m + n)) = --(&n)) /\
     (&m + &n = &(m + n))`,
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; INT_NEG_ADD] THEN
    REWRITE_TAC[INT_ADD_ASSOC; INT_ADD_LINV; INT_ADD_LID] THEN
    REWRITE_TAC[INT_ADD_RINV; INT_ADD_LID] THEN
    ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
    REWRITE_TAC[INT_ADD_ASSOC; INT_ADD_LINV; INT_ADD_LID] THEN
    REWRITE_TAC[INT_ADD_RINV; INT_ADD_LID]) in
  GEN_REWRITE_CONV I [pth0] ORELSEC
  (fun tm ->
    try let l,r = dest tm in
        if not(is_intconst l) || not(is_intconst r) then failwith ""
        else if rator l = neg_tm then
          if rator r = neg_tm then
            let th1 = INST [rand(rand l),m_tm; rand(rand r),n_tm] pth1 in
            let tm1 = rand(rand(rand(concl th1))) in
            let th2 = AP_TERM neg_tm (AP_TERM amp_tm (NUM_ADD_CONV tm1)) in
            TRANS th1 th2
          else
            let m = rand(rand l) and n = rand r in
            let m' = dest_numeral m and n' = dest_numeral n in
            if m' <=/ n' then
              let p = mk_numeral (n' -/ m') in
              let th1 = INST [m,m_tm; p,n_tm] pth2 in
              let th2 = NUM_ADD_CONV (rand(rand(lhand(concl th1)))) in
              let th3 = AP_TERM (rator tm) (AP_TERM amp_tm (SYM th2)) in
              TRANS th3 th1
            else
              let p = mk_numeral (m' -/ n') in
              let th1 = INST [n,m_tm; p,n_tm] pth3 in
              let th2 = NUM_ADD_CONV (rand(rand(lhand(lhand(concl th1))))) in
              let th3 = AP_TERM neg_tm (AP_TERM amp_tm (SYM th2)) in
              let th4 = AP_THM (AP_TERM add_tm th3) (rand tm) in
              TRANS th4 th1
        else
          if rator r = neg_tm then
            let m = rand l and n = rand(rand r) in
            let m' = dest_numeral m and n' = dest_numeral n in
            if n' <=/ m' then
              let p = mk_numeral (m' -/ n') in
              let th1 = INST [n,m_tm; p,n_tm] pth4 in
              let th2 = NUM_ADD_CONV (rand(lhand(lhand(concl th1)))) in
              let th3 = AP_TERM add_tm (AP_TERM amp_tm (SYM th2)) in
              let th4 = AP_THM th3 (rand tm) in
              TRANS th4 th1
            else
             let p = mk_numeral (n' -/ m') in
             let th1 = INST [m,m_tm; p,n_tm] pth5 in
             let th2 = NUM_ADD_CONV (rand(rand(rand(lhand(concl th1))))) in
             let th3 = AP_TERM neg_tm (AP_TERM amp_tm (SYM th2)) in
             let th4 = AP_TERM (rator tm) th3 in
             TRANS th4 th1
          else
            let th1 = INST [rand l,m_tm; rand r,n_tm] pth6 in
            let tm1 = rand(rand(concl th1)) in
            let th2 = AP_TERM amp_tm (NUM_ADD_CONV tm1) in
            TRANS th1 th2
    with Failure _ -> failwith "INT_ADD_CONV");;

let INT_SUB_CONV =
  GEN_REWRITE_CONV I [INT_SUB] THENC
  TRY_CONV(RAND_CONV INT_NEG_CONV) THENC
  INT_ADD_CONV;;

let INT_POW_CONV =
  let pth1,pth2 = (CONJ_PAIR o prove)
   (`(&x pow n = &(x EXP n)) /\
     ((--(&x)) pow n = if EVEN n then &(x EXP n) else --(&(x EXP n)))`,
    REWRITE_TAC[INT_OF_NUM_POW; INT_POW_NEG]) in
  let tth = prove
   (`((if T then x:int else y) = x) /\ ((if F then x:int else y) = y)`,
    REWRITE_TAC[]) in
  let neg_tm = `(--)` in
  (GEN_REWRITE_CONV I [pth1] THENC RAND_CONV NUM_EXP_CONV) ORELSEC
  (GEN_REWRITE_CONV I [pth2] THENC
   RATOR_CONV(RATOR_CONV(RAND_CONV NUM_EVEN_CONV)) THENC
   GEN_REWRITE_CONV I [tth] THENC
   (fun tm -> if rator tm = neg_tm then RAND_CONV(RAND_CONV NUM_EXP_CONV) tm
              else RAND_CONV NUM_EXP_CONV  tm));;

let INT_ABS_CONV =
  let pth = prove
   (`(abs(--(&x)) = &x) /\
     (abs(&x) = &x)`,
    REWRITE_TAC[INT_ABS_NEG; INT_ABS_NUM]) in
  GEN_REWRITE_CONV I [pth];;

let INT_MAX_CONV =
  REWR_CONV INT_MAX THENC
  RATOR_CONV(RATOR_CONV(RAND_CONV INT_LE_CONV)) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES];;

let INT_MIN_CONV =
  REWR_CONV INT_MIN THENC
  RATOR_CONV(RATOR_CONV(RAND_CONV INT_LE_CONV)) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES];;

let INT_SGN_CONV =
  GEN_REWRITE_CONV I [INT_SGN] THENC
  RATOR_CONV(LAND_CONV INT_LT_CONV) THENC
  (GEN_REWRITE_CONV I [CONJUNCT1(SPEC_ALL COND_CLAUSES)] ORELSEC
   (GEN_REWRITE_CONV I [CONJUNCT2(SPEC_ALL COND_CLAUSES)] THENC
    RATOR_CONV(LAND_CONV INT_LT_CONV) THENC
    GEN_REWRITE_CONV I [COND_CLAUSES]));;

(* ------------------------------------------------------------------------- *)
(* Instantiate the normalizer.                                               *)
(* ------------------------------------------------------------------------- *)

let INT_POLY_CONV =
  let sth = prove
   (`(!x y z. x + (y + z) = (x + y) + z) /\
     (!x y. x + y = y + x) /\
     (!x. &0 + x = x) /\
     (!x y z. x * (y * z) = (x * y) * z) /\
     (!x y. x * y = y * x) /\
     (!x. &1 * x = x) /\
     (!x. &0 * x = &0) /\
     (!x y z. x * (y + z) = x * y + x * z) /\
     (!x. x pow 0 = &1) /\
     (!x n. x pow (SUC n) = x * x pow n)`,
    REWRITE_TAC[INT_POW] THEN INT_ARITH_TAC)
  and rth = prove
   (`(!x. --x = --(&1) * x) /\
     (!x y. x - y = x + --(&1) * y)`,
    INT_ARITH_TAC)
  and is_semiring_constant = is_intconst
  and SEMIRING_ADD_CONV = INT_ADD_CONV
  and SEMIRING_MUL_CONV = INT_MUL_CONV
  and SEMIRING_POW_CONV = INT_POW_CONV in
  let _,_,_,_,_,INT_POLY_CONV =
    SEMIRING_NORMALIZERS_CONV sth rth
     (is_semiring_constant,
      SEMIRING_ADD_CONV,SEMIRING_MUL_CONV,SEMIRING_POW_CONV)
     (<) in
  INT_POLY_CONV;;

(* ------------------------------------------------------------------------- *)
(* Instantiate the ring and ideal procedures.                                *)
(* ------------------------------------------------------------------------- *)

let INT_RING,int_ideal_cofactors =
  let INT_INTEGRAL = prove
   (`(!x. &0 * x = &0) /\
     (!x y z. (x + y = x + z) <=> (y = z)) /\
     (!w x y z. (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))`,
    REWRITE_TAC[MULT_CLAUSES; EQ_ADD_LCANCEL] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ;
                GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
    ONCE_REWRITE_TAC[GSYM INT_SUB_0] THEN
    REWRITE_TAC[GSYM INT_ENTIRE] THEN INT_ARITH_TAC)
  and int_ty = `:int` in
  let pure,ideal =
  RING_AND_IDEAL_CONV
      (dest_intconst,mk_intconst,INT_EQ_CONV,
       `(--):int->int`,`(+):int->int->int`,`(-):int->int->int`,
       genvar bool_ty,`(*):int->int->int`,genvar bool_ty,
       `(pow):int->num->int`,
       INT_INTEGRAL,TRUTH,INT_POLY_CONV) in
  pure,
  (fun tms tm -> if forall (fun t -> type_of t = int_ty) (tm::tms)
                 then ideal tms tm
                 else failwith
                  "int_ideal_cofactors: not all terms have type :int");;

(* ------------------------------------------------------------------------- *)
(* Set up overloading so we can use same symbols for N, Z and even R.        *)
(* ------------------------------------------------------------------------- *)

make_overloadable "divides" `:A->A->bool`;;
make_overloadable "mod" `:A->A->A->bool`;;
make_overloadable "coprime" `:A#A->bool`;;
make_overloadable "gcd" `:A#A->A`;;
make_overloadable "lcm" `:A#A->A`;;

(* ------------------------------------------------------------------------- *)
(* The general notion of congruence: just syntax for equivalence relation.   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("==",(10,"right"));;

let cong = new_definition
  `(x == y) (rel:A->A->bool) <=> rel x y`;;

(* ------------------------------------------------------------------------- *)
(* Get real moduli defined and out of the way first.                         *)
(* ------------------------------------------------------------------------- *)

let real_mod = new_definition
  `real_mod n (x:real) y = ?q. integer q /\ x - y = q * n`;;

overload_interface ("mod",`real_mod`);;

(* ------------------------------------------------------------------------- *)
(* Integer divisibility.                                                     *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("divides",(12,"right"));;
overload_interface("divides",`int_divides:int->int->bool`);;

let int_divides = new_definition
  `a divides b <=> ?x:int. b = a * x`;;

let INT_DIVIDES_LE = prove
 (`!x y:int. x divides y ==> abs(x) <= abs(y) \/ y = &0`,
  SIMP_TAC[int_divides; LEFT_IMP_EXISTS_THM; INT_ABS_MUL; INT_ENTIRE] THEN
  REWRITE_TAC[TAUT `p \/ q \/ r <=> ~q /\ ~r ==> p`] THEN
  REWRITE_TAC[INT_ARITH `x:int <= x * y <=> &0 <= x * (y - &1)`] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_LE_MUL THEN ASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Integer congruences.                                                      *)
(* ------------------------------------------------------------------------- *)

parse_as_prefix "mod";;
overload_interface ("mod",`int_mod:int->int->int->bool`);;

let int_mod = new_definition
  `(mod n) x y = n divides (x - y)`;;

let int_congruent = prove
 (`!x y n. (x == y) (mod n) <=> ?d. x - y = n * d`,
  REWRITE_TAC[int_mod; cong; int_divides]);;

let INT_CONG_IMP_EQ = prove
 (`!x y n:int. abs(x - y) < n /\ (x == y) (mod n) ==> x = y`,
  REWRITE_TAC[int_congruent; GSYM int_divides] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN
  ASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Integer coprimality.                                                      *)
(* ------------------------------------------------------------------------- *)

overload_interface("coprime",`int_coprime:int#int->bool`);;

let int_coprime = new_definition
 `!a b. coprime(a,b) <=> ?x y. a * x + b * y = &1`;;

(* ------------------------------------------------------------------------- *)
(* A tactic for simple divisibility/congruence/coprimality goals.            *)
(* ------------------------------------------------------------------------- *)

let INTEGER_TAC =
  let int_ty = `:int` in
  let INT_POLYEQ_CONV =
    GEN_REWRITE_CONV I [GSYM INT_SUB_0] THENC LAND_CONV INT_POLY_CONV in
  let ISOLATE_VARIABLE =
    let pth = INT_ARITH `!a x. a = &0 <=> x = x + a` in
    let is_defined v t =
      let mons = striplist(dest_binary "int_add") t in
      mem v mons && forall (fun m -> v = m || not(free_in v m)) mons in
    fun vars tm ->
      let th = INT_POLYEQ_CONV tm
      and th' = (SYM_CONV THENC INT_POLYEQ_CONV) tm in
      let v,th1 =
          try find (fun v -> is_defined v (lhand(rand(concl th)))) vars,th'
          with Failure _ ->
              find (fun v -> is_defined v (lhand(rand(concl th')))) vars,th in
      let th2 = TRANS th1 (SPECL [lhs(rand(concl th1)); v] pth) in
      CONV_RULE(RAND_CONV(RAND_CONV INT_POLY_CONV)) th2 in
  let UNWIND_POLYS_CONV tm =
    let vars,bod = strip_exists tm in
    let cjs = conjuncts bod in
    let th1 = tryfind (ISOLATE_VARIABLE vars) cjs in
    let eq = lhand(concl th1) in
    let bod' = list_mk_conj(eq::(subtract cjs [eq])) in
    let th2 = CONJ_ACI_RULE(mk_eq(bod,bod')) in
    let th3 = TRANS th2 (MK_CONJ th1 (REFL(rand(rand(concl th2))))) in
    let v = lhs(lhand(rand(concl th3))) in
    let vars' = (subtract vars [v]) @ [v] in
    let th4 = CONV_RULE(RAND_CONV(REWR_CONV UNWIND_THM2)) (MK_EXISTS v th3) in
    let IMP_RULE v v' =
     DISCH_ALL(itlist SIMPLE_CHOOSE v (itlist SIMPLE_EXISTS v' (ASSUME bod))) in
    let th5 = IMP_ANTISYM_RULE (IMP_RULE vars vars') (IMP_RULE vars' vars) in
    TRANS th5 (itlist MK_EXISTS (subtract vars [v]) th4) in
  let zero_tm = `&0` and one_tm = `&1` in
  let isolate_monomials =
    let mul_tm = `(int_mul)` and add_tm = `(int_add)`
    and neg_tm = `(int_neg)` in
    let dest_mul = dest_binop mul_tm
    and dest_add = dest_binop add_tm
    and mk_mul = mk_binop mul_tm
    and mk_add = mk_binop add_tm in
    let scrub_var v m =
      let ps = striplist dest_mul m in
      let ps' = subtract ps [v] in
      if ps' = [] then one_tm else end_itlist mk_mul ps' in
    let find_multipliers v mons =
      let mons1 = filter (fun m -> free_in v m) mons in
      let mons2 = map (scrub_var v) mons1 in
      if mons2 = [] then zero_tm else end_itlist mk_add mons2 in
    fun vars tm ->
      let cmons,vmons =
         partition (fun m -> intersect (frees m) vars = [])
                   (striplist dest_add tm) in
      let cofactors = map (fun v -> find_multipliers v vmons) vars
      and cnc = if cmons = [] then zero_tm
                else mk_comb(neg_tm,end_itlist mk_add cmons) in
      cofactors,cnc in
  let isolate_variables evs ps eq =
    let vars = filter (fun v -> vfree_in v eq) evs in
    let qs,p = isolate_monomials vars eq in
    let rs = filter (fun t -> type_of t = int_ty) (qs @ ps) in
    let rs = int_ideal_cofactors rs p in
    eq,zip (fst(chop_list(length qs) rs)) vars in
  let subst_in_poly i p = rhs(concl(INT_POLY_CONV (vsubst i p))) in
  let rec solve_idealism evs ps eqs =
    if evs = [] then [] else
    let eq,cfs = tryfind (isolate_variables evs ps) eqs in
    let evs' = subtract evs (map snd cfs)
    and eqs' = map (subst_in_poly cfs) (subtract eqs [eq]) in
    cfs @ solve_idealism evs' ps eqs' in
  let rec GENVAR_EXISTS_CONV tm =
    if not(is_exists tm) then REFL tm else
    let ev,bod = dest_exists tm in
    let gv = genvar(type_of ev) in
    (GEN_ALPHA_CONV gv THENC BINDER_CONV GENVAR_EXISTS_CONV) tm in
  let EXISTS_POLY_TAC (asl,w as gl) =
    let evs,bod = strip_exists w
    and ps = mapfilter (check (fun t -> type_of t = int_ty) o
                        lhs o concl o snd) asl in
    let cfs = solve_idealism evs ps (map lhs (conjuncts bod)) in
    (MAP_EVERY EXISTS_TAC(map (fun v -> rev_assocd v cfs zero_tm) evs) THEN
     REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC INT_RING) gl in
  let SCRUB_NEQ_TAC = MATCH_MP_TAC o MATCH_MP (MESON[]
    `~(x = y) ==> x = y \/ p ==> p`) in
  REWRITE_TAC[int_coprime; int_congruent; int_divides] THEN
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM;
              LEFT_OR_EXISTS_THM; RIGHT_OR_EXISTS_THM] THEN
  CONV_TAC(REPEATC UNWIND_POLYS_CONV) THEN
  REPEAT(FIRST_X_ASSUM SCRUB_NEQ_TAC) THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM;
              LEFT_OR_EXISTS_THM; RIGHT_OR_EXISTS_THM] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POLYEQ_CONV) THEN
  REWRITE_TAC[GSYM INT_ENTIRE;
              TAUT `a \/ (b /\ c) <=> (a \/ b) /\ (a \/ c)`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REPEAT DISCH_TAC THEN CONV_TAC GENVAR_EXISTS_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POLYEQ_CONV) THEN EXISTS_POLY_TAC;;

let INTEGER_RULE tm = prove(tm,INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* More div and rem properties.                                              *)
(* ------------------------------------------------------------------------- *)

let INT_DIVMOD_UNIQ = prove
 (`!m n q r. m = q * n + r /\ &0 <= r /\ r < abs n
             ==> m div n = q /\ m rem n = r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(n = &0)` MP_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o SPEC `m:int` o MATCH_MP INT_DIVISION) THEN
  ASM_CASES_TAC `m div n = q` THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC INT_RING; ALL_TAC] THEN
  SUBGOAL_THEN `abs(m rem n - r) < abs n` MP_TAC THENL
   [ASM_INT_ARITH_TAC; MATCH_MP_TAC(TAUT `~p ==> p ==> q`)] THEN
  MATCH_MP_TAC(INT_ARITH
   `&1 * abs n <= abs(q - m div n) * abs n /\
    abs(m rem n - r) = abs((q - m div n) * n)
    ==> ~(abs(m rem n - r) < abs n)`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INT_LE_RMUL THEN ASM_INT_ARITH_TAC;
    AP_TERM_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC INT_RING]);;

let INT_DIV_UNIQ = prove
 (`!m n q r. m = q * n + r /\ &0 <= r /\ r < abs n
             ==> m div n = q`,
  MESON_TAC[INT_DIVMOD_UNIQ]);;

let INT_REM_UNIQ = prove
 (`!m n q r. m = q * n + r /\ &0 <= r /\ r < abs n
             ==> m rem n = r`,
    MESON_TAC[INT_DIVMOD_UNIQ]);;

let INT_DIV_LT,INT_REM_LT = (CONJ_PAIR o prove)
 (`(!m n. (~(n = &0) ==> &0 <= m) /\ m < n ==> m div n = &0) /\
   (!m n. (~(n = &0) ==> &0 <= m) /\ m < n ==> m rem n = m)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `n:int = &0` THEN ASM_REWRITE_TAC[INT_DIV_0; INT_REM_0] THEN
  REWRITE_TAC[TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  STRIP_TAC THEN MATCH_MP_TAC INT_DIVMOD_UNIQ THEN ASM_INT_ARITH_TAC);;

let INT_DIV_RNEG,INT_REM_RNEG = (CONJ_PAIR o prove)
 (`(!m n. m div (--n) = --(m div n)) /\
   (!m n. m rem (--n) = m rem n)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `n:int = &0` THEN
  ASM_REWRITE_TAC[INT_DIV_0; INT_REM_0; INT_NEG_0] THEN
  MATCH_MP_TAC INT_DIVMOD_UNIQ THEN
  MP_TAC(SPECL [`m:int`; `n:int`] INT_DIVISION) THEN
  ASM_INT_ARITH_TAC);;

let INT_REM_RABS = prove
 (`!x y. x rem (abs y) = x rem y`,
  REWRITE_TAC[FORALL_INT_CASES; INT_ABS_NEG; INT_REM_RNEG; INT_ABS_NUM]);;

let INT_REM_REM = prove
 (`!m n. (m rem n) rem n = m rem n`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `n:int = &0` THEN ASM_REWRITE_TAC[INT_REM_0] THEN
  MATCH_MP_TAC INT_REM_UNIQ THEN EXISTS_TAC `&0:int` THEN
  REWRITE_TAC[INT_MUL_LZERO; INT_ADD_LID] THEN
  ASM_MESON_TAC[INT_DIVISION]);;

let INT_REM_EQ = prove
 (`!m n p. m rem p = n rem p <=> (m == n) (mod p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_congruent] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `m div p - n div p` THEN
    MP_TAC(SPECL [`m:int`; `p:int`] INT_DIVISION_SIMP) THEN
    MP_TAC(SPECL [`n:int`; `p:int`] INT_DIVISION_SIMP) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_RING;
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; INT_EQ_SUB_RADD] THEN
    X_GEN_TAC `d:int` THEN DISCH_THEN SUBST1_TAC THEN
    ASM_CASES_TAC `p:int = &0` THEN
    ASM_REWRITE_TAC[INT_REM_0; INT_MUL_LZERO; INT_ADD_LID] THEN
    MATCH_MP_TAC INT_REM_UNIQ THEN EXISTS_TAC `n div p + d` THEN
    MP_TAC(SPECL [`n:int`; `p:int`] INT_DIVISION) THEN
    ASM_SIMP_TAC[] THEN CONV_TAC INT_RING]);;

let INT_DIV_ZERO,INT_REM_ZERO = (CONJ_PAIR o prove)
 (`(!n. &0 div n = &0) /\ (!n. &0 rem n = &0)`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
  ASM_CASES_TAC `n:int = &0` THEN ASM_REWRITE_TAC[INT_DIV_0; INT_REM_0] THEN
  MATCH_MP_TAC INT_DIVMOD_UNIQ THEN
  ASM_INT_ARITH_TAC);;

let INT_REM_EQ_0 = prove
 (`!m n. m rem n = &0 <=> n divides m`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPEC `n:int` INT_REM_ZERO)) THEN
  REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE);;

let INT_MUL_DIV_EQ = prove
 (`(!m n. n * m div n = m <=> n divides m) /\
   (!m n. m div n * n = m <=> n divides m)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`m:int`; `n:int`] INT_DIVISION_SIMP) THEN
  REWRITE_TAC[GSYM INT_REM_EQ_0] THEN CONV_TAC INT_RING);;

let INT_CONG_LREM = prove
 (`!x y n. (x rem n == y) (mod n) <=> (x == y) (mod n)`,
  REWRITE_TAC[GSYM INT_REM_EQ; INT_REM_REM]);;

let INT_CONG_RREM = prove
 (`!x y n. (x == y rem n) (mod n) <=> (x == y) (mod n)`,
  REWRITE_TAC[GSYM INT_REM_EQ; INT_REM_REM]);;

let INT_REM_MOD_SELF = prove
 (`!m n. (m rem n == m) (mod n)`,
  REWRITE_TAC[INT_CONG_LREM] THEN CONV_TAC INTEGER_RULE);;

let INT_REM_REM_MUL = prove
 (`(!m n p. m rem (n * p) rem n = m rem n) /\
   (!m n p. m rem (n * p) rem p = m rem p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INT_REM_EQ] THENL
   [MP_TAC(ISPECL [`m:int`; `n * p:int`] INT_REM_MOD_SELF);
    MP_TAC(ISPECL [`m:int`; `n * p:int`] INT_REM_MOD_SELF)] THEN
  CONV_TAC INTEGER_RULE);;

let INT_CONG_SOLVE_BOUNDS = prove
 (`!a n:int. ~(n = &0) ==> ?x. &0 <= x /\ x < abs n /\ (x == a) (mod n)`,
  MESON_TAC[INT_DIVISION; INT_REM_MOD_SELF]);;

let INT_NEG_REM = prove
 (`!n p. --(n rem p) rem p = --n rem p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(a:int == b) (mod n) ==> (--a == --b) (mod n)`) THEN
  REWRITE_TAC[INT_REM_MOD_SELF]);;

let INT_ADD_REM = prove
 (`!m n p. (m rem p + n rem p) rem p = (m + n) rem p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_REM_EQ] THEN MATCH_MP_TAC(INTEGER_RULE
   `(x:int == x') (mod n) /\ (y == y') (mod n)
    ==> (x + y == x' + y') (mod n)`) THEN
  REWRITE_TAC[INT_REM_MOD_SELF]);;

let INT_SUB_REM = prove
 (`!m n p. (m rem p - n rem p) rem p = (m - n) rem p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_REM_EQ] THEN MATCH_MP_TAC(INTEGER_RULE
   `(x:int == x') (mod n) /\ (y == y') (mod n)
    ==> (x - y == x' - y') (mod n)`) THEN
  REWRITE_TAC[INT_REM_MOD_SELF]);;

let INT_MUL_REM = prove
 (`!m n p. (m rem p * n rem p) rem p = (m * n) rem p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_REM_EQ] THEN MATCH_MP_TAC(INTEGER_RULE
   `(x:int == x') (mod n) /\ (y == y') (mod n)
    ==> (x * y == x' * y') (mod n)`) THEN
  REWRITE_TAC[INT_REM_MOD_SELF]);;

let INT_POW_REM = prove
 (`!m n p. ((m rem p) pow n) rem p = (m pow n) rem p`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[INT_POW] THEN
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM INT_MUL_REM] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[INT_REM_REM] THEN
  REWRITE_TAC[INT_MUL_REM]);;

let INT_OF_NUM_DIV,INT_OF_NUM_REM = (CONJ_PAIR o prove)
 (`(!m n. &m div &n = &(m DIV n)) /\
   (!m n. &m rem &n = &(m MOD n))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[INT_DIV_0; INT_REM_0; DIV_ZERO; MOD_ZERO] THEN
  MATCH_MP_TAC INT_DIVMOD_UNIQ THEN
  REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD; INT_ABS_NUM] THEN
  REWRITE_TAC[INT_POS; INT_OF_NUM_EQ; INT_OF_NUM_LT] THEN
  MATCH_MP_TAC DIVISION THEN ASM_REWRITE_TAC[]);;

let INT_DIV_REFL,INT_REM_REFL = (CONJ_PAIR o prove)
 (`(!n. n div n = if n = &0 then &0 else &1) /\
   (!n. n rem n = &0)`,
  REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `n:int` THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[INT_DIV_0; INT_REM_0]; ALL_TAC] THEN
  MATCH_MP_TAC INT_DIVMOD_UNIQ THEN ASM_INT_ARITH_TAC);;

let INT_DIV_LNEG,INT_REM_LNEG = (CONJ_PAIR o prove)
 (`(!m n. --m div n =
          if m rem n = &0 then --(m div n) else --(m div n) - int_sgn n) /\
   (!m n. --m rem n =
          if m rem n = &0 then &0 else abs n - m rem n)`,
  REWRITE_TAC[AND_FORALL_THM] THEN MAP_EVERY X_GEN_TAC [`m:int`; `n:int`] THEN
  ASM_CASES_TAC `n:int = &0` THENL
   [ASM_REWRITE_TAC[INT_DIV_0; INT_REM_0; INT_SGN_0] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC INT_DIVMOD_UNIQ THEN
  FIRST_ASSUM(MP_TAC o SPEC `m:int` o MATCH_MP INT_DIVISION) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_SGN_ABS_ALT; INT_ARITH
   `--m:int = (--x - y) * z + w <=> m = x * z + y * z - w`] THEN
  ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC);;

let INT_DIV_NEG2 = prove
 (`!m n. --m div --n = if m rem n = &0 then m div n else m div n + int_sgn n`,
  REWRITE_TAC[INT_DIV_RNEG; INT_DIV_LNEG; INT_SGN_NEG; INT_REM_RNEG] THEN
  INT_ARITH_TAC);;

let INT_REM_NEG2 = prove
 (`!m n. --m rem --n = if m rem n = &0 then &0 else abs n - m rem n`,
  REWRITE_TAC[INT_REM_LNEG; INT_REM_RNEG] THEN INT_ARITH_TAC);;

let INT_DIV_1,INT_REM_1 = (CONJ_PAIR o prove)
 (`(!n. n div &1 = n) /\
   (!n. n rem &1 = &0)`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC INT_DIVMOD_UNIQ THEN INT_ARITH_TAC);;

let INT_DIV_MUL,INT_REM_MUL = (CONJ_PAIR o prove)
 (`((!m n. ~(n = &0) ==> (m * n) div n = m) /\
    (!m n. ~(m = &0) ==> (m * n) div m = n)) /\
   ((!m n. (m * n) rem n = &0) /\
    (!m n. (m * n) rem m = &0))`,
  MATCH_MP_TAC(TAUT
   `((p ==> p') /\ (q ==> q')) /\ p /\ q ==> (p /\ p') /\ (q /\ q')`) THEN
  CONJ_TAC THENL [MESON_TAC[INT_MUL_SYM]; REWRITE_TAC[AND_FORALL_THM]] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n:int = &0` THEN
  ASM_REWRITE_TAC[INT_REM_0; INT_MUL_RZERO] THEN
  MATCH_MP_TAC INT_DIVMOD_UNIQ THEN ASM_INT_ARITH_TAC);;

let INT_DIV_LT_EQ = prove
 (`!a b c. &0 < a ==> (b div a < c <=> b < a * c)`,
  GEN_REWRITE_TAC I [FORALL_INT_CASES] THEN
  REWRITE_TAC[INT_ARITH `~(&0:int < -- &n)`] THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; INT_OF_NUM_LT] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [FORALL_INT_CASES] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_DIV; FORALL_INT_CASES] THEN
    REWRITE_TAC[INT_MUL_RNEG; INT_OF_NUM_MUL] THEN
    REWRITE_TAC[INT_OF_NUM_LT; INT_ARITH `~(&m:int < -- &n)`] THEN
    ASM_SIMP_TAC[RDIV_LT_EQ; LE_1];
    DISCH_TAC] THEN
  X_GEN_TAC `m:num` THEN
  REWRITE_TAC[INT_DIV_LNEG] THEN COND_CASES_TAC THENL
   [MP_TAC(SPECL [`&m:int`; `&n:int`] INT_DIVISION) THEN
    MAP_EVERY ABBREV_TAC [`q = &m div &n`; `r = &m rem &n`] THEN
    ASM_SIMP_TAC[INT_OF_NUM_EQ; LE_1] THEN DISCH_TAC THEN
    REWRITE_TAC[INT_ARITH `--(q * &n + &0:int) = &n * --q`] THEN
    ASM_SIMP_TAC[INT_LT_LMUL_EQ; INT_OF_NUM_LT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INT_SGN; INT_OF_NUM_LT; LE_1] THEN
  REWRITE_TAC[INT_LT_SUB_RADD; GSYM INT_LE_DISCRETE] THEN
  ASM_REWRITE_TAC[INT_ARITH `--a:int <= b <=> ~(a < --b)`] THEN
  REWRITE_TAC[INT_ARITH
   `(~(m:int < n * --c) <=> --m < n * c) <=> ~(m = n * --c)`] THEN
  ASM_MESON_TAC[INT_REM_MUL]);;

let INT_LE_DIV_EQ = prove
 (`!a b c. &0 < a ==> (c <= b div a <=> a * c <= b)`,
  SIMP_TAC[GSYM INT_NOT_LT; INT_DIV_LT_EQ]);;

let INT_DIV_LE_EQ = prove
 (`!a b c. &0 < a ==> (b div a <= c <=> b < a * (c + &1))`,
  SIMP_TAC[INT_LE_DISCRETE; INT_DIV_LT_EQ]);;

let INT_LT_DIV_EQ = prove
 (`!a b c. &0 < a ==> (c < b div a <=> a * (c + &1) <= b)`,
  SIMP_TAC[GSYM INT_NOT_LE; INT_DIV_LE_EQ]);;

let INT_DIV_LE = prove
 (`!m n. abs(m div n) <= abs m`,
  GEN_REWRITE_TAC BINDER_CONV [FORALL_INT_CASES] THEN
  REWRITE_TAC[INT_DIV_RNEG; INT_ABS_NEG] THEN
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[INT_DIV_0; INT_ABS_NUM; INT_ABS_POS] THEN
  REWRITE_TAC[INT_ARITH `abs(x:int) <= a <=> --a <= x /\ x <= a`] THEN
  ASM_SIMP_TAC[INT_LE_DIV_EQ; INT_DIV_LE_EQ; INT_OF_NUM_LT; LE_1] THEN
  X_GEN_TAC `m:int` THEN MATCH_MP_TAC(INT_ARITH
   `&0:int < n /\ abs m * &1 <= abs m * n
    ==> n * --abs m <= m /\ m < n * (abs m + &1)`) THEN
  ASM_SIMP_TAC[INT_OF_NUM_LT; LE_1] THEN
  MATCH_MP_TAC INT_LE_LMUL THEN REWRITE_TAC[INT_ABS_POS] THEN
  ASM_SIMP_TAC[INT_OF_NUM_LE; LE_1]);;

let INT_DIV_DIV,INT_REM_MUL_REM = (CONJ_PAIR o prove)
 (`(!m n p. &0 <= n ==> (m div n) div p = m div (n * p)) /\
   (!m n p. &0 <= n ==> m rem (n * p) = n * (m div n) rem p + m rem n)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `n:int = &0` THEN
  ASM_REWRITE_TAC[INT_MUL_LZERO; INT_DIV_0; INT_REM_0;
                  INT_DIV_ZERO; INT_ADD_LID; INT_LE_LT] THEN
  ASM_CASES_TAC `&0:int < n` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `p:int = &0` THEN
  ASM_REWRITE_TAC[INT_MUL_RZERO; INT_DIV_0; INT_REM_0] THENL
   [REWRITE_TAC[INT_REM_DIV] THEN INT_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN
  MATCH_MP_TAC INT_DIVMOD_UNIQ THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[INT_REM_DIV] THEN INT_ARITH_TAC;
    ASM_SIMP_TAC[INT_LE_ADD; INT_LE_MUL; INT_LT_IMP_LE; INT_DIVISION];
    TRANS_TAC INT_LTE_TRANS `n * (abs p - &1) + n:int` THEN CONJ_TAC THENL
     [MATCH_MP_TAC INT_LET_ADD2 THEN ASM_SIMP_TAC[INT_LT_REM] THEN
      ASM_SIMP_TAC[INT_LE_LMUL_EQ; INT_LE_SUB_LADD; GSYM INT_LT_DISCRETE] THEN
      ASM_SIMP_TAC[INT_DIVISION];
      REWRITE_TAC[INT_ARITH `n * (p - &1) + n:int = n * p`; INT_ABS_MUL] THEN
      MATCH_MP_TAC INT_LE_RMUL THEN INT_ARITH_TAC]]);;

let INT_DIV_EQ_0 = prove
 (`!m n. m div n = &0 <=> n = &0 \/ &0 <= m /\ m < abs n`,
  GEN_REWRITE_TAC BINDER_CONV [FORALL_INT_CASES] THEN
  REWRITE_TAC[INT_DIV_RNEG; INT_NEG_EQ_0; INT_ABS_NEG] THEN
  MAP_EVERY X_GEN_TAC [`m:int`; `n:num`] THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[INT_DIV_0; INT_OF_NUM_EQ; INT_ABS_NUM] THEN
  ASM_SIMP_TAC[GSYM INT_LE_ANTISYM; INT_DIV_LE_EQ; INT_LE_DIV_EQ; CONJ_SYM;
               INT_OF_NUM_LT; LE_1; INT_ADD_LID; INT_MUL_RZERO; INT_MUL_RID]);;

let INT_REM_EQ_SELF = prove
 (`!m n. m rem n = m <=> n = &0 \/ &0 <= m /\ m < abs n`,
  REWRITE_TAC[INT_REM_DIV; INT_ARITH `m - x:int = m <=> x = &0`] THEN
  REWRITE_TAC[INT_DIV_EQ_0; INT_ENTIRE] THEN INT_ARITH_TAC);;

let INT_REM_UNIQUE = prove
 (`!m n p. m rem n = p <=>
           (n = &0 /\ m = p \/ &0 <= p /\ p < abs n) /\ (m == p) (mod n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n:int = &0` THENL
   [ASM_REWRITE_TAC[INT_REM_0; INT_ABS_0; INT_LET_ANTISYM] THEN
    CONV_TAC INTEGER_RULE;
    EQ_TAC THENL
     [DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[INT_DIVISION] THEN
      REWRITE_TAC[GSYM INT_REM_EQ; INT_REM_REM];
      ASM_SIMP_TAC[GSYM INT_REM_EQ; INT_REM_EQ_SELF]]]);;

let INT_DIV_REM = prove
 (`!m n p. &0 <= n ==> (m div n) rem p = (m rem (n * p)) div n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n:int = &0` THEN
  ASM_REWRITE_TAC[INT_LE_LT; INT_DIV_0; INT_REM_ZERO] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[INT_REM_MUL_REM; INT_LT_IMP_LE] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_DIV_UNIQ THEN
  EXISTS_TAC `m rem n` THEN ASM_SIMP_TAC[INT_DIVISION] THEN
  REWRITE_TAC[INT_ADD_AC; INT_MUL_AC]);;

let INT_REM_REM_LE = prove
 (`!m n p. ~(n = &0) /\ abs n <= abs p ==> m rem n rem p = m rem n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INT_REM_EQ_SELF] THEN
  ASM_CASES_TAC `p:int = &0` THEN ASM_REWRITE_TAC[INT_REM_POS_EQ] THEN
  TRANS_TAC INT_LTE_TRANS `abs n:int` THEN ASM_MESON_TAC[INT_DIVISION]);;

let INT_LE_DIV = prove
 (`!m n. &0 <= m /\ &0 <= n ==> &0 <= m div n`,
  REWRITE_TAC[GSYM INT_FORALL_POS; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[INT_OF_NUM_DIV; INT_POS]);;

let INT_LT_DIV = prove
 (`!m n. &0 < n /\ n <= m ==> &0 < m div n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[INT_ARITH `&0:int < x <=> &0 <= x /\ ~(x = &0)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INT_LE_DIV THEN ASM_INT_ARITH_TAC;
    REWRITE_TAC[INT_DIV_EQ_0] THEN ASM_INT_ARITH_TAC]);;

let INT_REM_LE_EQ = prove
 (`!m n. m rem n <= m <=> n = &0 \/ &0 <= m`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n:int = &0` THEN
  ASM_SIMP_TAC[INT_REM_0; INT_LE_REFL] THEN
  EQ_TAC THENL [ASM_MESON_TAC[INT_REM_POS; INT_LE_TRANS]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM INT_REM_RABS] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`m:int`; `n:int`] THEN
  REWRITE_TAC[GSYM INT_FORALL_POS; GSYM INT_FORALL_ABS] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM; MOD_LE]);;

let INT_REM_LE = prove
 (`!m n p. (n = &0 \/ &0 <= m) /\ m <= p ==> m rem n <= p`,
  MESON_TAC[INT_REM_LE_EQ; INT_LE_TRANS]);;

let INT_REM_MUL_ADD = prove
 (`(!m n p. (m * n + p) rem n = p rem n) /\
   (!m n p. (n * m + p) rem n = p rem n) /\
   (!m n p. (p + m * n) rem n = p rem n) /\
   (!m n p. (p + n * m) rem n = p rem n)`,
  ONCE_REWRITE_TAC[GSYM INT_ADD_REM] THEN
  REWRITE_TAC[INT_REM_MUL; INT_ADD_LID; INT_ADD_RID; INT_REM_REM]);;

let INT_DIV_MUL_ADD = prove
 (`(!m n p. ~(n = &0) ==> (m * n + p) div n = m + p div n) /\
   (!m n p. ~(n = &0) ==> (n * m + p) div n = m + p div n) /\
   (!m n p. ~(n = &0) ==> (p + m * n) div n = p div n + m) /\
   (!m n p. ~(n = &0) ==> (p + n * m) div n = p div n + m)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_DIV_UNIQ THEN
  EXISTS_TAC `p rem n` THEN
  MP_TAC(SPECL [`p:int`; `n:int`] INT_DIVISION) THEN
  ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC);;

let INT_CONG_DIV2 = prove
 (`!a b m n.
      (a == b) (mod (m * n)) ==> (a div m == b div m) (mod n)`,
  GEN_REWRITE_TAC (funpow 2 BINDER_CONV) [FORALL_INT_CASES] THEN
  REWRITE_TAC[INT_DIV_RNEG; INT_MUL_LNEG;
     INTEGER_RULE `(--a:int == --b) (mod n) <=> (a == b) (mod n)`;
     INTEGER_RULE `(a:int == b) (mod(--n)) <=> (a == b) (mod n)`] THEN
  SIMP_TAC[GSYM INT_REM_EQ; INT_DIV_REM; INT_POS]);;

let INT_REM_2_CASES = prove
 (`!n. n rem &2 = &0 \/ n rem &2 = &1`,
  GEN_TAC THEN MP_TAC(SPECL [`n:int`; `&2:int`] INT_DIVISION) THEN
  INT_ARITH_TAC);;

let NOT_INT_REM_2 = prove
 (`(!n. ~(n rem &2 = &0) <=> n rem &2 = &1) /\
   (!n. ~(n rem &2 = &1) <=> n rem &2 = &0)`,
  REWRITE_TAC[AND_FORALL_THM] THEN MP_TAC INT_REM_2_CASES THEN
  MATCH_MP_TAC MONO_FORALL THEN INT_ARITH_TAC);;

let INT_REM_2_DIVIDES = prove
 (`(!n. n rem &2 = &0 <=> &2 divides n) /\
   (!n. n rem &2 = &1 <=> ~(&2 divides n))`,
  REWRITE_TAC[GSYM(CONJUNCT1 NOT_INT_REM_2)] THEN
  REWRITE_TAC[INT_REM_EQ_0]);;

let INT_REM_2_EXPAND = prove
 (`!x. x rem &2 = if &2 divides x then &0 else &1`,
  MESON_TAC[INT_REM_2_DIVIDES]);;

let INT_REM_2_NEG = prove
 (`!x. --x rem &2 = x rem &2`,
  GEN_TAC THEN REWRITE_TAC[INT_REM_2_EXPAND] THEN
  REWRITE_TAC[INTEGER_RULE `(a:int) divides --x <=> a divides x`]);;

let INT_DIVIDES_DIV_SELF = prove
 (`!n d. d divides n ==> n div d divides n`,
  MESON_TAC[INT_MUL_DIV_EQ; int_divides]);;

let INT_DIV_BY_DIV = prove
 (`!m n:int. ~(n = &0) /\ m divides n ==> n div (n div m) = m`,
  MESON_TAC[INT_DIVIDES_DIV_SELF; INT_MUL_DIV_EQ; INT_RING
    `a * x:int = n /\ a * y = n /\ ~(n = &0) ==> x = y`]);;

let INT_DIVIDES_DIV_DIVIDES = prove
 (`!n d e. d divides n /\ (n = &0 ==> e = &0)
           ==> (n div d divides e <=> n divides d * e)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM(CONJUNCT1 INT_MUL_DIV_EQ)] THEN
  ASM_CASES_TAC `e:int = &0` THEN ASM_REWRITE_TAC[] THEN INTEGER_TAC);;

let INT_DIVIDES_DIVIDES_DIV = prove
 (`!n d e. d divides n ==> (e divides (n div d) <=> (d * e) divides n)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(CONJUNCT1 INT_MUL_DIV_EQ)] THEN
  ASM_CASES_TAC `d:int = &0` THEN ASM_REWRITE_TAC[INT_DIV_ZERO; INT_DIV_0] THEN
  INTEGER_TAC);;

let INT_DIVIDES_DIVIDES_DIV_EQ = prove
 (`!n d e. d divides n /\ e divides (n div d) <=> (d * e) divides n`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(r ==> p) /\ (p ==> (q <=> r)) ==> (p /\ q <=> r)`) THEN
  REWRITE_TAC[INT_DIVIDES_DIVIDES_DIV] THEN INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic operations also on div and rem, hence the whole lot.           *)
(* ------------------------------------------------------------------------- *)

let INT_DIV_CONV,INT_REM_CONV =
  let pth = prove
   (`q * n + r = m ==> &0 <= r ==> r < abs n ==> m div n = q /\ m rem n = r`,
    MESON_TAC[INT_DIVMOD_UNIQ])
  and m = `m:int` and n = `n:int` and q = `q:int` and r = `r:int`
  and dtm = `(div)` and mtm = `(rem)` in
  let emod_num x y =
    let r = mod_num x y in
    if r </ num 0 then r +/ abs_num y else r in
  let equo_num x y = quo_num (x -/ emod_num x y) y in
  let INT_DIVMOD_CONV x y =
    let k = equo_num x y
    and l = emod_num x y in
    let th0 = INST [mk_intconst x,m; mk_intconst y,n;
                    mk_intconst k,q; mk_intconst l,r] pth in
    let tm0 = lhand(lhand(concl th0)) in
    let th1 = (LAND_CONV INT_MUL_CONV THENC INT_ADD_CONV) tm0 in
    let th2 = MP th0 th1 in
    let tm2 = lhand(concl th2) in
    let th3 = MP th2 (EQT_ELIM(INT_LE_CONV tm2)) in
    let tm3 = lhand(concl th3) in
    MP th3 (EQT_ELIM((RAND_CONV INT_ABS_CONV THENC INT_LT_CONV) tm3)) in
  (fun tm -> try let l,r = dest_binop dtm tm in
                 CONJUNCT1(INT_DIVMOD_CONV (dest_intconst l) (dest_intconst r))
             with Failure _ -> failwith "INT_DIV_CONV"),
  (fun tm -> try let l,r = dest_binop mtm tm in
                 CONJUNCT2(INT_DIVMOD_CONV (dest_intconst l) (dest_intconst r))
             with Failure _ -> failwith "INT_MOD_CONV");;

let int_red_conv_list =
    [`x <= y`,INT_LE_CONV;
     `x < y`,INT_LT_CONV;
     `x >= y`,INT_GE_CONV;
     `x > y`,INT_GT_CONV;
     `x:int = y`,INT_EQ_CONV;
     `--x`,CHANGED_CONV INT_NEG_CONV;
     `int_sgn(x)`,INT_SGN_CONV;
     `abs(x)`,INT_ABS_CONV;
     `x + y`,INT_ADD_CONV;
     `x - y`,INT_SUB_CONV;
     `x * y`,INT_MUL_CONV;
     `x div y`,INT_DIV_CONV;
     `x rem y`,INT_REM_CONV;
     `x pow n`,INT_POW_CONV;
     `max x y`,INT_MAX_CONV;
     `min x y`,INT_MIN_CONV];;

let INT_RED_CONV =
  let gconv_net = itlist (uncurry net_of_conv) int_red_conv_list
    (basic_net()) in
  REWRITES_CONV gconv_net;;

let INT_REDUCE_CONV = DEPTH_CONV INT_RED_CONV;;

let int_compute_add_convs =
  let convlist = map (fun pat,the_conv ->
    let c,args = strip_comb pat in (c,length args,the_conv))
    int_red_conv_list in
  fun (compset:Compute.compset) ->
    itlist (fun newc () -> Compute.add_conv newc compset) convlist ();;

let INT_COMPUTE_CONV =
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  int_compute_add_convs cs;
  Compute.WEAK_CBV_CONV cs;;

(* ------------------------------------------------------------------------- *)
(* Integer analogs of the usual even/odd combining theorems EVEN_ADD etc.    *)
(* ------------------------------------------------------------------------- *)

let INT_2_DIVIDES_ADD = prove
 (`!m n:int. &2 divides (m + n) <=> (&2 divides m <=> &2 divides n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_REM_2_DIVIDES] THEN
  ONCE_REWRITE_TAC[GSYM INT_ADD_REM] THEN
  DISJ_CASES_TAC(SPEC `m:int` INT_REM_2_CASES) THEN
  DISJ_CASES_TAC(SPEC `n:int` INT_REM_2_CASES) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV);;

let INT_2_DIVIDES_SUB = prove
 (`!m n:int. &2 divides (m - n) <=> (&2 divides m <=> &2 divides n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_REM_2_DIVIDES] THEN
  ONCE_REWRITE_TAC[GSYM INT_SUB_REM] THEN
  DISJ_CASES_TAC(SPEC `m:int` INT_REM_2_CASES) THEN
  DISJ_CASES_TAC(SPEC `n:int` INT_REM_2_CASES) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV);;

let INT_2_DIVIDES_MUL = prove
 (`!m n:int. &2 divides (m * n) <=> &2 divides m \/ &2 divides n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_REM_2_DIVIDES] THEN
  ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN
  DISJ_CASES_TAC(SPEC `m:int` INT_REM_2_CASES) THEN
  DISJ_CASES_TAC(SPEC `n:int` INT_REM_2_CASES) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV);;

let INT_2_DIVIDES_POW = prove
 (`!n k. &2 divides (n pow k) <=> &2 divides n /\ ~(k = 0)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[INT_POW] THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 INT_REM_2_DIVIDES)] THEN
    CONV_TAC INT_REDUCE_CONV;
    ASM_REWRITE_TAC[INT_2_DIVIDES_MUL; NOT_SUC] THEN
    CONV_TAC TAUT]);;

(* ------------------------------------------------------------------------- *)
(* Pushing and pulling to combine nested rem terms into a single rem.        *)
(* ------------------------------------------------------------------------- *)

let INT_REM_DOWN_CONV =
  let addmul_conv = GEN_REWRITE_CONV I
    [GSYM INT_NEG_REM; GSYM INT_ADD_REM; GSYM INT_SUB_REM;
     GSYM INT_MUL_REM; GSYM INT_POW_REM]
  and mod_conv = GEN_REWRITE_CONV I [INT_REM_REM] in
  let rec downconv tm =
   ((addmul_conv THENC LAND_CONV downconv) ORELSEC
    (mod_conv THENC downconv) ORELSEC
    SUB_CONV downconv) tm
  and upconv =
    GEN_REWRITE_CONV DEPTH_CONV
     [INT_NEG_REM; INT_ADD_REM; INT_SUB_REM; INT_MUL_REM;
      INT_POW_REM; INT_REM_REM] in
  downconv THENC upconv;;

(* ------------------------------------------------------------------------- *)
(* Reduction of (a pow k) rem n keeping intermediates reduced.               *)
(* ------------------------------------------------------------------------- *)

let INT_POW_REM_CONV =
  let pth_0,pth_1 = (CONJ_PAIR o prove)
   (`((&m pow k) rem &n = &(m EXP k MOD n) /\
      (&m pow k) rem (-- &n) = &(m EXP k MOD n)) /\
     ((-- &m pow k) rem &n =
      if EVEN k then &(m EXP k MOD n) else (-- &(m EXP k MOD n)) rem &n) /\
     ((-- &m pow k) rem (-- &n) =
      if EVEN k then &(m EXP k MOD n) else (-- &(m EXP k MOD n)) rem &n)`,
    REWRITE_TAC[INT_REM_RNEG; INT_POW_NEG] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REFL_TAC) in
  let conv =
    (GEN_REWRITE_CONV I [pth_0] THENC RAND_CONV EXP_MOD_CONV) ORELSEC
    (GEN_REWRITE_CONV I [pth_1] THENC
     RATOR_CONV(LAND_CONV NUM_EVEN_CONV) THENC
     GEN_REWRITE_CONV I [COND_CLAUSES] THENC
     (RAND_CONV EXP_MOD_CONV ORELSEC
      (LAND_CONV
       (RAND_CONV(RAND_CONV EXP_MOD_CONV THENC TRY_CONV INT_NEG_CONV)) THENC
        INT_REM_CONV))) in
  fun tm ->
    match tm with
      Comb(Comb(Const("rem",_),
                Comb(Comb(Const("int_pow",_),m),k)),n)
      when is_intconst m && is_numeral k && is_intconst n -> conv tm
  | _ -> failwith "INT_POW_REM_CONV";;

(* ------------------------------------------------------------------------- *)
(* Existence of integer gcd, and the Bezout identity.                        *)
(* ------------------------------------------------------------------------- *)

let WF_INT_MEASURE = prove
 (`!P m. (!x. &0 <= m(x)) /\ (!x. (!y. m(y) < m(x) ==> P(y)) ==> P(x))
         ==> !x:A. P(x)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `!n x:A. m(x) = &n ==> P(x)` MP_TAC THENL
   [MATCH_MP_TAC num_WF; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT; INT_FORALL_POS] THEN ASM_MESON_TAC[]);;

let WF_INT_MEASURE_2 = prove
 (`!P m. (!x y. &0 <= m x y) /\
         (!x y. (!x' y'. m x' y' < m x y ==> P x' y') ==> P x y)
         ==> !x:A y:B. P x y`,
  REWRITE_TAC[FORALL_UNCURRY; GSYM FORALL_PAIR_THM; WF_INT_MEASURE]);;

let INT_GCD_EXISTS = prove
 (`!a b. ?d. d divides a /\ d divides b /\ ?x y. d = a * x + b * y`,
  let INT_GCD_EXISTS_CASES = INT_ARITH
   `(a = &0 \/ b = &0) \/
    abs(a - b) + abs b < abs a + abs b \/ abs(a + b) + abs b < abs a + abs b \/
    abs a + abs(b - a) < abs a + abs b \/ abs a + abs(b + a) < abs a + abs b` in
  MATCH_MP_TAC WF_INT_MEASURE_2 THEN EXISTS_TAC `\x y. abs(x) + abs(y)` THEN
  REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
  DISJ_CASES_THEN MP_TAC INT_GCD_EXISTS_CASES THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[INTEGER_RULE `d divides &0`] THEN
    REWRITE_TAC[INT_MUL_LZERO; INT_ADD_LID; INT_ADD_RID] THEN
    MESON_TAC[INTEGER_RULE `d divides d`; INT_MUL_RID];
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (ANTE_RES_THEN MP_TAC)) THEN
    MATCH_MP_TAC MONO_EXISTS THEN INTEGER_TAC]);;

let INT_GCD_EXISTS_POS = prove
 (`!a b. ?d. &0 <= d /\ d divides a /\ d divides b /\ ?x y. d = a * x + b * y`,
  REPEAT GEN_TAC THEN
  X_CHOOSE_TAC `d:int` (SPECL [`a:int`; `b:int`] INT_GCD_EXISTS) THEN
  DISJ_CASES_TAC(SPEC `d:int` INT_LE_NEGTOTAL) THEN
  ASM_MESON_TAC[INTEGER_RULE `(--d) divides x <=> d divides x`;
                INT_ARITH `a * --x + b * --y = --(a * x + b * y)`]);;

(* ------------------------------------------------------------------------- *)
(* Hence define (positive) integer gcd and lcm operations, with a few        *)
(* basic properties of the latter; most analogous gcd ones get automated.    *)
(* ------------------------------------------------------------------------- *)

overload_interface("gcd",`int_gcd:int#int->int`);;
overload_interface("lcm",`int_lcm:int#int->int`);;

let int_gcd = new_specification ["int_gcd"]
 (REWRITE_RULE[EXISTS_UNCURRY; SKOLEM_THM] INT_GCD_EXISTS_POS);;

let int_lcm = new_definition
 `int_lcm(m,n) = if m * n = &0 then &0 else abs(m * n) div gcd(m,n)`;;

let INT_DIVIDES_LABS = prove
 (`!d n. abs(d) divides n <=> d divides n`,
  REPEAT GEN_TAC THEN SIMP_TAC[INT_ABS] THEN COND_CASES_TAC THEN INTEGER_TAC);;

let INT_DIVIDES_RABS = prove
 (`!d n. d divides (abs n) <=> d divides n`,
  REPEAT GEN_TAC THEN SIMP_TAC[INT_ABS] THEN COND_CASES_TAC THEN INTEGER_TAC);;

let INT_DIVIDES_ABS = prove
 (`(!d n. abs(d) divides n <=> d divides n) /\
   (!d n. d divides (abs n) <=> d divides n)`,
  REWRITE_TAC[INT_DIVIDES_LABS; INT_DIVIDES_RABS]);;

let INT_LCM_POS = prove
 (`!m n. &0 <= lcm(m,n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_lcm] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[INT_POS; INT_ABS_POS; INT_LE_DIV; int_gcd]);;

let INT_MUL_GCD_LCM = prove
 (`!m n:int. gcd(m,n) * lcm(m,n) = abs(m * n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_lcm] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_MUL_RZERO; INT_ABS_NUM] THEN
  REWRITE_TAC[INT_MUL_DIV_EQ] THEN REWRITE_TAC[INT_ABS] THEN
  ASM_MESON_TAC[int_gcd; INTEGER_RULE
   `d divides m ==> d divides (m * n:int) /\ d divides --(m * n)`]);;

let INT_MUL_LCM_GCD = prove
 (`!m n:int. lcm(m,n) * gcd(m,n) = abs(m * n)`,
  MESON_TAC[INT_MUL_SYM; INT_MUL_GCD_LCM]);;

let INT_DIVIDES_LCM_GCD = prove
 (`!m n d:int. d divides lcm(m,n) <=> d * gcd(m,n) divides m * n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_lcm] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [INTEGER_TAC; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
    INT_DIVIDES_DIVIDES_DIV o lhand o snd) THEN
  ASM_REWRITE_TAC[INT_ABS_ZERO; INT_DIVIDES_ABS] THEN ANTS_TAC THENL
   [MESON_TAC[int_gcd; INTEGER_RULE `d divides m ==> d divides (m * n:int)`];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_MUL_SYM]]);;

let INT_LCM_DIVIDES = prove
 (`!m n d:int. lcm(m,n) divides d <=> m divides d /\ n divides d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_lcm] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [INTEGER_TAC; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
    INT_DIVIDES_DIV_DIVIDES o lhand o snd) THEN
  ASM_REWRITE_TAC[INT_ABS_ZERO; INT_DIVIDES_ABS] THEN ANTS_TAC THENL
   [MESON_TAC[int_gcd; INTEGER_RULE `d divides m ==> d divides (m * n:int)`];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`m:int`; `n:int`] int_gcd) THEN INTEGER_TAC);;

let INT_LCM = prove
 (`!m n. m divides lcm(m,n) /\
         n divides lcm(m,n) /\
         (!d. m divides d /\ n divides d ==> lcm(m,n) divides d)`,
  REWRITE_TAC[INT_LCM_DIVIDES; INT_DIVIDES_LCM_GCD] THEN
  REPEAT GEN_TAC THEN MP_TAC(SPECL [`m:int`; `n:int`] int_gcd) THEN
  INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Add their elimination to INTEGER_TAC (better for gcd at the moment).      *)
(* ------------------------------------------------------------------------- *)

let INTEGER_TAC =
  let GCD_ELIM_TAC =
    let gcd_tm = `gcd:int#int->int` in
    let dest_gcd tm =
      let l,r = dest_comb tm in
      if l = gcd_tm then dest_pair r else failwith "dest_gcd" in
    REPEAT GEN_TAC THEN
    W(fun (asl,w) ->
          let gts = find_terms (can dest_gcd) w in
          let ths = map
           (fun tm -> let a,b = dest_gcd tm in SPECL [a;b] int_gcd) gts in
          MAP_EVERY MP_TAC ths THEN
          MAP_EVERY SPEC_TAC (zip gts (map (genvar o type_of) gts))) in
  let pth = prove
   (`!d a b:int. d divides gcd(a,b) <=> d divides a /\ d divides b`,
    GCD_ELIM_TAC THEN INTEGER_TAC) in
  GEN_REWRITE_TAC TOP_DEPTH_CONV
   [pth; INT_DIVIDES_ABS; INT_DIVIDES_LCM_GCD; INT_LCM_DIVIDES] THEN
  REPEAT(GEN_TAC ORELSE CONJ_TAC) THEN GCD_ELIM_TAC THEN INTEGER_TAC;;

let INTEGER_RULE tm = prove(tm,INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Mapping from nonnegative integers back to natural numbers.                *)
(* ------------------------------------------------------------------------- *)

let num_of_int = new_definition
  `num_of_int x = @n. &n = x`;;

let NUM_OF_INT_OF_NUM = prove
 (`!n. num_of_int(&n) = n`,
  REWRITE_TAC[num_of_int; INT_OF_NUM_EQ; SELECT_UNIQUE]);;

let INT_OF_NUM_OF_INT = prove
 (`!x. &0 <= x ==> &(num_of_int x) = x`,
  REWRITE_TAC[GSYM INT_FORALL_POS; num_of_int] THEN
  GEN_TAC THEN CONV_TAC SELECT_CONV THEN MESON_TAC[]);;

let NUM_OF_INT = prove
 (`!x. &0 <= x <=> (&(num_of_int x) = x)`,
  MESON_TAC[INT_OF_NUM_OF_INT; INT_POS]);;

let NUM_OF_INT_ADD = prove
 (`!x y. &0 <= x /\ &0 <= y
         ==> num_of_int(x + y) = num_of_int x + num_of_int y`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  REWRITE_TAC[GSYM INT_FORALL_POS; INT_OF_NUM_ADD; NUM_OF_INT_OF_NUM]);;

let NUM_OF_INT_MUL = prove
 (`!x y. &0 <= x /\ &0 <= y
         ==> num_of_int(x * y) = num_of_int x * num_of_int y`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  REWRITE_TAC[GSYM INT_FORALL_POS; INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM]);;

let NUM_OF_INT_POW = prove
 (`!x n. &0 <= x ==> num_of_int(x pow n) = num_of_int x EXP n`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  REWRITE_TAC[GSYM INT_FORALL_POS; INT_OF_NUM_POW; NUM_OF_INT_OF_NUM]);;

(* ------------------------------------------------------------------------- *)
(* Now define similar notions over the natural numbers.                      *)
(* ------------------------------------------------------------------------- *)

overload_interface("divides",`num_divides:num->num->bool`);;
overload_interface ("mod",`num_mod:num->num->num->bool`);;
overload_interface("coprime",`num_coprime:num#num->bool`);;
overload_interface("gcd",`num_gcd:num#num->num`);;
overload_interface("lcm",`num_lcm:num#num->num`);;

let num_divides = new_definition
 `a divides b <=> &a divides &b`;;

let num_mod = new_definition
  `(mod n) x y <=> (mod &n) (&x) (&y)`;;

let num_congruent = prove
 (`!x y n. (x == y) (mod n) <=> (&x == &y) (mod &n)`,
  REWRITE_TAC[cong; num_mod]);;

let num_coprime = new_definition
 `coprime(a,b) <=> coprime(&a,&b)`;;

let num_gcd = new_definition
 `gcd(a,b) = num_of_int(gcd(&a,&b))`;;

let num_lcm = new_definition
 `lcm(a,b) = num_of_int(lcm(&a,&b))`;;

(* ------------------------------------------------------------------------- *)
(* Map an assertion over N to an integer equivalent.                         *)
(* To make this work nicely, all variables of type num should be quantified. *)
(* ------------------------------------------------------------------------- *)

let NUM_TO_INT_CONV =
  let pth_relativize = prove
   (`((!n. P(&n)) <=> (!i. ~(&0 <= i) \/ P i)) /\
     ((?n. P(&n)) <=> (?i. &0 <= i /\ P i))`,
    REWRITE_TAC[INT_EXISTS_POS; INT_FORALL_POS] THEN MESON_TAC[]) in
  let relation_conv = (GEN_REWRITE_CONV TOP_SWEEP_CONV o map GSYM)
   [INT_OF_NUM_EQ; INT_OF_NUM_LE; INT_OF_NUM_LT; INT_OF_NUM_GE; INT_OF_NUM_GT;
    INT_OF_NUM_SUC; INT_OF_NUM_ADD; INT_OF_NUM_MUL; INT_OF_NUM_POW]
  and quantifier_conv = GEN_REWRITE_CONV DEPTH_CONV [pth_relativize] in
  NUM_SIMPLIFY_CONV THENC relation_conv THENC quantifier_conv;;

(* ------------------------------------------------------------------------- *)
(* Linear decision procedure for the naturals at last!                       *)
(* ------------------------------------------------------------------------- *)

let ARITH_RULE =
  let init_conv =
    NUM_SIMPLIFY_CONV THENC
    GEN_REWRITE_CONV DEPTH_CONV [ADD1] THENC
    PROP_ATOM_CONV (BINOP_CONV NUM_NORMALIZE_CONV) THENC
    PRENEX_CONV THENC
    (GEN_REWRITE_CONV TOP_SWEEP_CONV o map GSYM)
      [INT_OF_NUM_EQ; INT_OF_NUM_LE; INT_OF_NUM_LT; INT_OF_NUM_GE;
       INT_OF_NUM_GT; INT_OF_NUM_ADD; SPEC `NUMERAL k` INT_OF_NUM_MUL;
       INT_OF_NUM_MAX; INT_OF_NUM_MIN]
  and is_numimage t =
    match t with
      Comb(Const("int_of_num",_),n) when not(is_numeral n) -> true
    | _ -> false in
  fun tm ->
    try
      let th1 = init_conv tm in
      let tm1 = rand(concl th1) in
      let avs,bod = strip_forall tm1 in
      let nim = setify(find_terms is_numimage bod) in
      let gvs = map (genvar o type_of) nim in
      let pths = map (fun v -> SPEC (rand v) INT_POS) nim in
      let ibod = itlist (curry mk_imp o concl) pths bod in
      let gbod = subst (zip gvs nim) ibod in
      let th2 = INST (zip nim gvs) (INT_ARITH gbod) in
      let th3 = GENL avs (rev_itlist (C MP) pths th2) in
      EQ_MP (SYM th1) th3
    with Failure msg ->
      failwith ("ARITH_RULE `" ^ (string_of_term tm) ^ "`: " ^ msg);;

let ARITH_TAC = CONV_TAC(EQT_INTRO o ARITH_RULE);;

let ASM_ARITH_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (not o is_forall o concl))) THEN
  ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* Enhanced integer procedures eliminating div and rem (replacing first one) *)
(* ------------------------------------------------------------------------- *)

let INT_ARITH =
  let atom_CONV =
    let pth = prove
      (`(~(x:int <= y) <=> y + &1 <= x) /\
        (~(x < y) <=> y <= x) /\
        (~(x = y) <=> x + &1 <= y \/ y + &1 <= x) /\
        (x < y <=> x + &1 <= y)`,
       REWRITE_TAC[INT_NOT_LE; INT_NOT_LT; INT_NOT_EQ; INT_LT_DISCRETE]) in
    GEN_REWRITE_CONV I [pth]
  and bub_CONV = GEN_REWRITE_CONV TOP_SWEEP_CONV
   [int_eq; int_le; int_lt; int_ge; int_gt;
    int_of_num_th; int_neg_th; int_add_th; int_mul_th;
    int_sub_th; int_pow_th; int_abs_th; int_max_th; int_min_th] in
  let base_CONV = TRY_CONV atom_CONV THENC bub_CONV in
  let NNF_NORM_CONV = GEN_NNF_CONV false
   (base_CONV,fun t -> base_CONV t,base_CONV(mk_neg t)) in
  let INT_POS_RULE =
    let x_tm = `x:int` and y_tm = `y:int` and n_tm = `n:num` in
    let pth_pos = SPEC n_tm INT_POS
    and pth_add = SPECL [x_tm;y_tm] INT_LE_ADD
    and pth_mul = SPECL [x_tm;y_tm] INT_LE_MUL
    and pth_pow = SPECL [x_tm;n_tm] INT_POW_LE in
    let rec rule tm =
      match tm with
        Comb(Const("int_of_num",_),rtm) -> INST[rtm,n_tm] pth_pos
      | Comb(Comb(Const("int_add",_),ltm),rtm) ->
            let lth = rule ltm and rth = rule rtm in
            MP (INST [ltm,x_tm; rtm,y_tm] pth_add) (CONJ lth rth)
      | Comb(Comb(Const("int_mul",_),ltm),rtm) ->
            let lth = rule ltm and rth = rule rtm in
            MP (INST [ltm,x_tm; rtm,y_tm] pth_mul) (CONJ lth rth)
      | Comb(Comb(Const("int_pow",_),ltm),rtm) ->
            let lth = rule ltm in
            MP (INST [ltm,x_tm; rtm,n_tm] pth_pow) lth
      | _ -> failwith "INT_POS_RULE" in
    rule in
  let INT_DIVREM_ELIM_CONV =
    let tac =
      REWRITE_TAC[GSYM INT_LT_DISCRETE] THEN
      ASM_CASES_TAC `n:int = &0` THEN ASM_REWRITE_TAC[] THENL
       [ASM_REWRITE_TAC[INT_ABS_NUM; INT_LET_ANTISYM] THEN
        REWRITE_TAC[UNWIND_THM2; GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM] THEN
        REWRITE_TAC[INT_DIV_0; INT_REM_0];
        EQ_TAC THEN STRIP_TAC THENL
         [MAP_EVERY EXISTS_TAC [`m div n`; `m rem n`] THEN
          ASM_SIMP_TAC[INT_DIVISION; INT_LE_DIV];
          ASM_METIS_TAC[INT_DIVMOD_UNIQ]]] in
    let DIVREM_ELIM_THM = prove
     (`P (m div n) (m rem n) <=>
       ?q r. (n = &0 /\ q = &0 /\ r = m \/
              m = q * n + r /\
              &0 <= r /\ r + &1 <= abs n) /\
             P q r`,
      tac)
    and DIVREM_ELIM_THM' = prove
     (`P (m div n) (m rem n) <=>
       ?q r. (n = &0 /\ q = &0 /\ r = m \/
              m = q * n + r /\
              (&0 <= m /\ &0 <= n ==> &0 <= q) /\
              &0 <= r /\ r + &1 <= abs n) /\
             P q r`,
      tac) in
    let DIVREM_ELIM_THM_POS = prove
     (`&0 <= m /\ &0 <= n
       ==> (P (m div n) (m rem n) <=>
            ?q r. (n = &0 /\ q = &0 /\ r = m \/
                   m = q * n + r /\
                   &0 <= q /\
                   &0 <= r /\ r + &1 <= n) /\
                  P q r)`,
      SIMP_TAC[DIVREM_ELIM_THM'; INT_ABS])
    and BETA2_CONV = RATOR_CONV BETA_CONV THENC BETA_CONV
    and div_tm = `(div):int->int->int`
    and rem_tm = `(rem):int->int->int`
    and p_tm = `P:int->int->bool`
    and m_tm = `m:int`
    and n_tm = `n:int` in
    let is_divrem =
      let is_div = is_binop div_tm and is_rem = is_binop rem_tm in
      fun tm -> is_div tm || is_rem tm in
    let rec conv tm =
      try let t = hd(sort free_in
           (find_terms (fun t -> is_divrem t && free_in t tm) tm)) in
          let x = lhand t and y = rand t in
          let dtm = mk_comb(mk_comb(div_tm,x),y)
          and rtm = mk_comb(mk_comb(rem_tm,x),y) in
          let vd = genvar(type_of dtm)
          and vr = genvar(type_of rtm) in
          let p = list_mk_abs([vd;vr],subst[vd,dtm; vr,rtm] tm) in
          let th0 = INST [p,p_tm; x,m_tm; y,n_tm] DIVREM_ELIM_THM_POS in
          let th1 =
            try let ltm,rtm = dest_conj(lhand(concl th0)) in
                MP th0
                 (CONJ (INT_POS_RULE(rand ltm)) (INT_POS_RULE(rand rtm)))
            with Failure _ -> INST [p,p_tm; x,m_tm; y,n_tm] DIVREM_ELIM_THM in
          let th2 = CONV_RULE(COMB2_CONV(RAND_CONV BETA2_CONV)
               (funpow 2 BINDER_CONV(RAND_CONV BETA2_CONV))) th1 in
          let th3 = CONV_RULE(RAND_CONV
                     (funpow 2 BINDER_CONV INT_REDUCE_CONV)) th2 in
           CONV_RULE(RAND_CONV(BINDER_CONV(BINDER_CONV(RAND_CONV conv)))) th3
      with Failure _ -> REFL tm in
    let rec topconv tm =
      if is_forall tm || is_exists tm then BINDER_CONV topconv tm
      else conv tm in
    topconv in
  let init_CONV =
    TOP_DEPTH_CONV BETA_CONV THENC
    PRESIMP_CONV THENC
    GEN_REWRITE_CONV DEPTH_CONV [INT_GT; INT_GE] THENC
    NNF_CONV THENC DEPTH_BINOP_CONV `(\/)` CONDS_ELIM_CONV THENC
    INT_REDUCE_CONV THENC INT_DIVREM_ELIM_CONV THENC
    NNF_NORM_CONV in
  let p_tm = `p:bool`
  and not_tm = `(~)` in
  let pth = TAUT(mk_eq(mk_neg(mk_neg p_tm),p_tm)) in
  fun tm ->
    try
      let th0 = INST [tm,p_tm] pth
      and th1 = init_CONV (mk_neg tm) in
      let th2 = REAL_ARITH(mk_neg(rand(concl th1))) in
      EQ_MP th0 (EQ_MP (AP_TERM not_tm (SYM th1)) th2)
    with Failure m ->
      failwith ("INT_ARITH `" ^ (string_of_term tm) ^ "`: " ^ m);;

let INT_ARITH_TAC = CONV_TAC(EQT_INTRO o INT_ARITH);;

let ASM_INT_ARITH_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (not o is_forall o concl))) THEN
  INT_ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* A few miscellaneous natural number lemmas.                                *)
(* ------------------------------------------------------------------------- *)

let BINARY_INDUCT = prove
 (`!P. P 0 /\ (!n. P n ==> P(2 * n) /\ P(2 * n + 1)) ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC num_WF THEN GEN_TAC THEN
  STRIP_ASSUME_TAC(ARITH_RULE
   `n = 0 \/ n DIV 2 < n /\ (n = 2 * n DIV 2 \/ n = 2 * n DIV 2 + 1)`) THEN
  ASM_MESON_TAC[]);;

let NUM_CASES_BINARY = prove
 (`!P. (!n. P n) <=> (!n. P(2 * n)) /\ (!n. P(2 * n + 1))`,
  MESON_TAC[ARITH_RULE `n = 2 * n DIV 2 \/ n = 2 * n DIV 2 + 1`]);;

let num_WF_DOWN = prove
 (`!P m:num.
        (!n. m <= n ==> P n) /\
        (!n. n < m /\ (!p. n < p ==> P p) ==> P n)
        ==> (!n. P n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `m = 0` THENL [ASM_MESON_TAC[LE_0]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. P(m - 1 - i)` MP_TAC THENL
   [MATCH_MP_TAC num_WF THEN GEN_TAC THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM MATCH_MP_TAC THEN ASSUME_TAC th) THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; X_GEN_TAC `p:num`] THEN
    ASM_CASES_TAC `m:num <= p` THEN ASM_SIMP_TAC[] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m - 1 - p`) THEN
    ASM_SIMP_TAC[ARITH_RULE
     `~(m <= p) ==> m - 1 - (m - 1 - p) = p`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ASM_MESON_TAC[ARITH_RULE `~(m <= n) ==> n = m - 1 - (m - 1 - n)`]]);;

let INT_REM_REM_POW_MIN = prove
 (`!x p m n. x rem (p pow m) rem (p pow n) = x rem (p pow MIN m n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:int = &0` THEN
  ASM_REWRITE_TAC[INT_REM_ZERO] THEN ASM_CASES_TAC `p:int = &0` THENL
   [ASM_REWRITE_TAC[INT_POW_ZERO; ARITH_RULE
     `MIN a b = 0 <=> a = 0 \/ b = 0`] THEN
    MAP_EVERY ASM_CASES_TAC [`m = 0`; `n = 0`] THEN
    ASM_REWRITE_TAC[INT_REM_0; INT_REM_1];
    REWRITE_TAC[ARITH_RULE `MIN m n = if n <= m then n else m`]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
    REWRITE_TAC[INT_POW_ADD; INT_REM_REM_MUL];
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE])] THEN
  MATCH_MP_TAC INT_REM_REM_LE THEN
  ASM_REWRITE_TAC[INT_POW_EQ_0; INT_ABS_POW] THEN
  MATCH_MP_TAC INT_POW_MONO THEN ASM_SIMP_TAC[LT_IMP_LE] THEN
  ASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Also a similar divisibility procedure for natural numbers.                *)
(* ------------------------------------------------------------------------- *)

let NUM_GCD = prove
 (`!a b. &(gcd(a,b)) = gcd(&a,&b)`,
  REWRITE_TAC[num_gcd; GSYM NUM_OF_INT; int_gcd]);;

let NUM_LCM = prove
 (`!a b. &(lcm(a,b)) = lcm(&a,&b)`,
  REWRITE_TAC[num_lcm; GSYM NUM_OF_INT; INT_LCM_POS]);;

let CONG = prove
 (`!x y n. (x == y) (mod n) <=> x MOD n = y MOD n`,
  REWRITE_TAC[num_congruent; GSYM INT_REM_EQ; INT_OF_NUM_REM; INT_OF_NUM_EQ]);;

let CONG_LMOD = prove
 (`!x y n. (x MOD n == y) (mod n) <=> (x == y) (mod n)`,
  REWRITE_TAC[CONG; MOD_MOD_REFL]);;

let CONG_RMOD = prove
 (`!x y n. (x == y MOD n) (mod n) <=> (x == y) (mod n)`,
  REWRITE_TAC[CONG; MOD_MOD_REFL]);;

let CONG_DIV2 = prove
 (`!a b m n. (a == b) (mod (m * n)) ==> (a DIV m == b DIV m) (mod n)`,
  SIMP_TAC[CONG; DIV_MOD]);;

let divides = prove
 (`a divides b <=> ?x:num. b = a * x`,
  REWRITE_TAC[num_divides; int_divides] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[INT_OF_NUM_MUL; INT_OF_NUM_EQ]] THEN
  DISCH_THEN(X_CHOOSE_TAC `x:int`) THEN EXISTS_TAC `num_of_int(abs x)` THEN
  SIMP_TAC[GSYM INT_OF_NUM_EQ;
           INT_ARITH `&m:int = &n <=> abs(&m :int) = abs(&n)`] THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_MUL; INT_ABS_MUL] THEN
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS; INT_ABS_ABS]);;

let DIVIDES_LE = prove
 (`!m n. m divides n ==> m <= n \/ n = 0`,
  SUBGOAL_THEN `!m n. m <= m * n \/ m * n = 0`
    (fun th -> MESON_TAC[divides; th]) THEN
  REWRITE_TAC[LE_MULT_LCANCEL; MULT_EQ_0; ARITH_RULE
   `m <= m * n <=> m * 1 <= m * n`] THEN
  ASM_ARITH_TAC);;

let DIVIDES_LE_STRONG = prove
 (`!m n. m divides n ==> 1 <= m /\ m <= n \/ n = 0`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `m = 0` THEN
  ASM_SIMP_TAC[DIVIDES_LE; LE_1; LE_0] THEN
  REWRITE_TAC[divides] THEN MESON_TAC[MULT_CLAUSES]);;

let DIVIDES_LE_IMP = prove
 (`!m n. m divides n /\ (n = 0 ==> m = 0) ==> m <= n`,
  MESON_TAC[DIVIDES_LE; LE_REFL]);;

let PROPERLY_DIVIDES_LE_IMP = prove
 (`!m n. m divides n /\ ~(n = 0) /\ ~(m = n) ==> 2 * m <= n`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  SIMP_TAC[IMP_CONJ; divides; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[NUM_RING `~(m = m * d) <=> ~(m = 0) /\ ~(d = 1)`] THEN
  SIMP_TAC[LE_MULT_LCANCEL; MULT_EQ_0] THEN ARITH_TAC);;

let DIVIDES_ANTISYM = prove
 (`!m n. m divides n /\ n divides m <=> m = n`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; REWRITE_TAC[divides] THEN MESON_TAC[MULT_CLAUSES]] THEN
  DISCH_THEN(CONJUNCTS_THEN(MP_TAC o MATCH_MP DIVIDES_LE_STRONG)) THEN
  ARITH_TAC);;

let DIVIDES_ONE = prove
 (`!n. n divides 1 <=> n = 1`,
  REWRITE_TAC[divides] THEN MESON_TAC[MULT_EQ_1; MULT_CLAUSES]);;

let DIV_ADD = prove
 (`!d a b. d divides a \/ d divides b
           ==> (a + b) DIV d = a DIV d + b DIV d`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `d = 0` THEN
  ASM_SIMP_TAC[DIV_ZERO; ADD_CLAUSES] THEN
  REWRITE_TAC[divides] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; DIV_MULT]);;

let DIVIDES_MOD = prove
 (`!m n. m divides n <=> n MOD m = 0`,
  REWRITE_TAC[divides; MOD_EQ_0] THEN MESON_TAC[MULT_SYM]);;

let DIVIDES_DIV_MULT = prove
 (`!m n. m divides n <=> ((n DIV m) * m = n)`,
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_DIV;
              INT_MUL_DIV_EQ; GSYM num_divides]);;

let DIV_BY_DIV = prove
 (`!m n. ~(n = 0) /\ m divides n ==> n DIV (n DIV m) = m`,
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_DIV; num_divides;
              INT_DIV_BY_DIV]);;

let DIVIDES_DIV_DIVIDES = prove
 (`!n d e. d divides n /\ (n = 0 ==> e = 0)
           ==> (n DIV d divides e <=> n divides d * e)`,
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_DIV; num_divides;
              GSYM INT_OF_NUM_MUL; INT_DIVIDES_DIV_DIVIDES]);;

let DIVIDES_DIV_SELF = prove
 (`!n d. d divides n ==> n DIV d divides n`,
  REWRITE_TAC[num_divides; GSYM INT_OF_NUM_DIV; INT_DIVIDES_DIV_SELF]);;

let DIVIDES_DIVIDES_DIV = prove
 (`!n d e. d divides n ==> (e divides (n DIV d) <=> (d * e) divides n)`,
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_DIV; num_divides;
              GSYM INT_OF_NUM_MUL; INT_DIVIDES_DIVIDES_DIV]);;

let DIVIDES_DIVIDES_DIV_EQ = prove
 (`!n d e:num. d divides n /\ e divides n DIV d <=> d * e divides n`,
  REWRITE_TAC[num_divides; GSYM INT_OF_NUM_DIV; GSYM INT_OF_NUM_MUL] THEN
  REWRITE_TAC[INT_DIVIDES_DIVIDES_DIV_EQ]);;

let DIVIDES_DIVIDES_DIV_IMP = prove
 (`!n d e. d * e divides n ==> e divides n DIV d`,
  MESON_TAC[DIVIDES_DIVIDES_DIV_EQ]);;

let MULT_DIV = prove
 (`(!m n p. p divides m ==> (m * n) DIV p = m DIV p * n) /\
   (!m n p. p divides n ==> (m * n) DIV p = m * n DIV p)`,
  MATCH_MP_TAC(TAUT `(a ==> b) /\ a ==> a /\ b`) THEN CONJ_TAC THENL
   [MESON_TAC[MULT_SYM]; SIMP_TAC[divides; LEFT_IMP_EXISTS_THM]] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p = 0` THEN
  ASM_SIMP_TAC[MULT_CLAUSES; DIV_0; GSYM MULT_ASSOC; DIV_MULT]);;

let NUMBER_TAC =
  let conva = GEN_REWRITE_CONV TRY_CONV [GSYM DIVIDES_ANTISYM] in
  let rec antisym_conv tm =
    if is_forall tm || is_exists tm then BINDER_CONV antisym_conv tm
    else if is_conj tm || is_disj tm then BINOP_CONV antisym_conv tm
    else if is_imp tm then RAND_CONV antisym_conv tm
    else conva tm in
  let pth_relativize = prove
   (`((!n. P(&n)) <=> (!i:int. &0 <= i ==> P i)) /\
     ((?n. P(&n)) <=> (?i:int. &0 <= i /\ P i))`,
    GEN_REWRITE_TAC RAND_CONV [TAUT `(a <=> b) <=> (~a <=> ~b)`] THEN
    REWRITE_TAC[NOT_EXISTS_THM; INT_FORALL_POS] THEN MESON_TAC[]) in
  let relation_conv =
   GEN_REWRITE_CONV TOP_SWEEP_CONV
    (num_divides::num_congruent::num_coprime::NUM_GCD::NUM_LCM::(map GSYM
    [INT_OF_NUM_EQ; INT_OF_NUM_LE; INT_OF_NUM_LT; INT_OF_NUM_GE; INT_OF_NUM_GT;
     INT_OF_NUM_SUC; INT_OF_NUM_ADD; INT_OF_NUM_MUL; INT_OF_NUM_POW]))
  and quantifier_conv = GEN_REWRITE_CONV DEPTH_CONV [pth_relativize] in
  REPEAT(CONJ_TAC ORELSE GEN_TAC ORELSE EQ_TAC) THEN CONV_TAC antisym_conv THEN
  W(fun (_,w) -> MAP_EVERY (fun v -> SPEC_TAC(v,v)) (frees w)) THEN
  CONV_TAC(relation_conv THENC quantifier_conv) THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN REPEAT GEN_TAC THEN
  INTEGER_TAC;;

let NUMBER_RULE tm = prove(tm,NUMBER_TAC);;

let COPRIME_LMOD = prove
 (`!a n. coprime(a MOD n,n) <=> coprime(a,n)`,
  MESON_TAC[CONG_LMOD; NUMBER_RULE `(x:num == x) (mod n)`; NUMBER_RULE
   `(a:num == b) (mod n) /\ coprime(a,n) ==> coprime(b,n)`]);;

let COPRIME_RMOD = prove
 (`!a n. coprime(n,a MOD n) <=> coprime(n,a)`,
  ONCE_REWRITE_TAC[NUMBER_RULE `coprime(a:num,b) <=> coprime(b,a)`] THEN
  REWRITE_TAC[COPRIME_LMOD]);;

let INT_CONG_NUM_EXISTS = prove
 (`!x y:int.
        (y = &0 ==> &0 <= x)
        ==> ?n. (&n == x) (mod y)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `num_of_int(x + abs(x * y))` THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INT_OF_NUM_OF_INT o
        lhand o rator o snd) THEN
  ANTS_TAC THENL
   [POP_ASSUM MP_TAC THEN ASM_CASES_TAC `y:int = &0` THEN
    ASM_REWRITE_TAC[] THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(INT_ARITH `abs(x) * &1:int <= y ==> &0 <= x + y`) THEN
    REWRITE_TAC[INT_ABS_MUL] THEN MATCH_MP_TAC INT_LE_LMUL THEN
    ASM_INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[INTEGER_RULE `(x + a:int == x) (mod n) <=> n divides a`] THEN
    REWRITE_TAC[INT_ABS] THEN COND_CASES_TAC THEN CONV_TAC INTEGER_RULE]);;

let GCD = prove
 (`!a b. (gcd(a,b) divides a /\ gcd(a,b) divides b) /\
         (!e. e divides a /\ e divides b ==> e divides gcd(a,b))`,
  NUMBER_TAC);;

let coprime = prove
 (`coprime(a,b) <=> !d. d divides a /\ d divides b ==> d = 1`,
  EQ_TAC THENL [CONV_TAC NUMBER_RULE; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `gcd(a,b)`) THEN REWRITE_TAC[GCD] THEN
  NUMBER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Definition (and not much more) of primality.                              *)
(* ------------------------------------------------------------------------- *)

let prime = new_definition
  `prime(p) <=> ~(p = 1) /\ !x. x divides p ==> x = 1 \/ x = p`;;

let ONE_OR_PRIME = prove
 (`!p. p = 1 \/ prime p <=> !n. n divides p ==> n = 1 \/ n = p`,
  GEN_TAC THEN REWRITE_TAC[prime] THEN
  ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[DIVIDES_ONE]);;

let ONE_OR_PRIME_DIVIDES_OR_COPRIME = prove
 (`!p. p = 1 \/ prime p <=> !n. p divides n \/ coprime(p,n)`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISJ1_TAC THEN CONV_TAC NUMBER_RULE;
    ASM_MESON_TAC[prime; coprime];
    REWRITE_TAC[ONE_OR_PRIME] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN ONCE_REWRITE_TAC[DISJ_SYM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN MATCH_MP_TAC MONO_OR THEN
    CONJ_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC NUMBER_RULE]);;

let PRIME_COPRIME_EQ_NONDIVISIBLE = prove
 (`!p. prime p <=> !n. coprime(p,n) <=> ~(p divides n)`,
  X_GEN_TAC `p:num` THEN ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[prime] THEN DISCH_THEN(MP_TAC o SPEC `1`) THEN
    MATCH_MP_TAC(TAUT `p /\ q ==> (p <=> ~q) ==> F`) THEN CONV_TAC NUMBER_RULE;
    MP_TAC(SPEC `p:num` ONE_OR_PRIME_DIVIDES_OR_COPRIME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    EQ_TAC THEN MATCH_MP_TAC MONO_FORALL THEN SIMP_TAC[TAUT `p \/ ~p`] THEN
    GEN_TAC THEN MATCH_MP_TAC(TAUT `~(p /\ q) ==> q \/ p ==> (p <=> ~q)`) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[CONTRAPOS_THM] THEN
    CONV_TAC NUMBER_RULE]);;

let ZERO_ONE_OR_PRIME_DIVPROD = prove
 (`!p a b.
        p = 0 \/ p = 1 \/ prime p
        ==> (p divides (a * b) <=> p divides a \/ p divides b)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[NUMBER_RULE `1 divides n`] THEN
  ASM_REWRITE_TAC[NUMBER_RULE `0 divides n <=> n = 0`; MULT_EQ_0] THEN
  EQ_TAC THENL [ALL_TAC; CONV_TAC NUMBER_RULE] THEN
  ASM_MESON_TAC[prime; coprime; NUMBER_RULE
   `!d a b:num. d divides (a * b) /\ coprime(d,a) ==> d divides b`]);;

let ZERO_ONE_OR_PRIME = prove
 (`!p. p = 0 \/ p = 1 \/ prime p <=>
       !a b. p divides (a * b) ==> p divides a \/ p divides b`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[ZERO_ONE_OR_PRIME_DIVPROD] THEN
  DISCH_TAC THEN REWRITE_TAC[TAUT `p \/ q <=> ~p ==> q`] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[prime; divides; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `b:num`]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; MULT_EQ_1; DE_MORGAN_THM]) THEN
  REWRITE_TAC[NUMBER_RULE `(n:num) divides n`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE_STRONG) THEN
  ONCE_REWRITE_TAC[ARITH_RULE `a * b <= a <=> a * b <= a * 1`;
                   ARITH_RULE `a * b <= b <=> a * b <= 1 * b`]THEN
  REWRITE_TAC[LE_MULT_LCANCEL; LE_MULT_RCANCEL] THEN
  ASM_SIMP_TAC[MULT_CLAUSES; ARITH_RULE `n <= 1 <=> n = 0 \/ n = 1`]);;

(* ------------------------------------------------------------------------- *)
(* Integer powers of real numbers.                                           *)
(* ------------------------------------------------------------------------- *)

make_overloadable "zpow" `:A->int->A`;;
parse_as_infix("zpow",(24,"left"));;
overload_interface ("zpow",`real_zpow:real->int->real`);;

let real_zpow = new_definition
 `(z:real) zpow (i:int) = if &0 <= i then z pow (num_of_int i)
                          else inv(z pow (num_of_int(--i)))`;;

let REAL_POW_ZPOW = prove
 (`!x n. x pow n = x zpow (&n)`,
  REWRITE_TAC[real_zpow; INT_POS; NUM_OF_INT_OF_NUM]);;

let REAL_ZPOW_NUM = prove
 (`!x n. x zpow (&n) = x pow n`,
  REWRITE_TAC[real_zpow; INT_POS; NUM_OF_INT_OF_NUM]);;

let REAL_ZPOW_0 = prove
 (`!x:real. x zpow (&0) = &1`,
  REWRITE_TAC[REAL_ZPOW_NUM; real_pow]);;

let REAL_ZPOW_1 = prove
 (`!x:real. x zpow (&1) = x`,
  REWRITE_TAC[REAL_ZPOW_NUM; REAL_POW_1]);;

let REAL_ZPOW_2 = prove
 (`!x:real. x zpow (&2) = x * x`,
  REWRITE_TAC[REAL_ZPOW_NUM; REAL_POW_2]);;

let REAL_ZPOW_ONE = prove
 (`!n. &1 zpow n = &1`,
  REWRITE_TAC[real_zpow; REAL_POW_ONE; REAL_INV_1; COND_ID]);;

let REAL_ZPOW_NEG = prove
 (`!x n. x zpow (--n) = inv(x zpow n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n:int = &0` THEN
  ASM_REWRITE_TAC[INT_NEG_0; REAL_ZPOW_0; REAL_INV_1] THEN
  ASM_SIMP_TAC[real_zpow; COND_SWAP; INT_NEG_NEG; INT_ARITH
   `~(n:int = &0) ==> (&0 <= --n <=> ~(&0 <= n))`] THEN
  MESON_TAC[REAL_INV_INV]);;

let REAL_ZPOW_MINUS1 = prove
 (`!x. x zpow --(&1) = inv x`,
  REWRITE_TAC[REAL_ZPOW_NEG; REAL_ZPOW_1]);;

let REAL_ZPOW_ZERO = prove
 (`!n. &0 zpow n = if n = &0 then &1 else &0`,
  REWRITE_TAC[FORALL_INT_CASES; REAL_ZPOW_NEG; REAL_ZPOW_NUM] THEN
  REWRITE_TAC[REAL_POW_ZERO; INT_NEG_EQ_0; INT_OF_NUM_EQ] THEN
  MESON_TAC[REAL_INV_0; REAL_INV_1]);;

let REAL_ZPOW_POW = prove
 (`(!(x:real) n. x zpow (&n) = x pow n) /\
   (!(x:real) n. x zpow (-- &n) = inv(x pow n))`,
  REWRITE_TAC[REAL_ZPOW_NEG; REAL_ZPOW_NUM]);;

let REAL_INV_ZPOW = prove
 (`!(x:real) n. inv(x zpow n) = inv(x) zpow n`,
  REWRITE_TAC[FORALL_INT_CASES; REAL_ZPOW_POW] THEN
  REWRITE_TAC[REAL_INV_POW; REAL_INV_INV]);;

let REAL_ZPOW_INV = prove
 (`!(x:real) n. inv x zpow n = inv(x zpow n)`,
  REWRITE_TAC[REAL_INV_ZPOW]);;

let REAL_ZPOW_ZPOW = prove
 (`!(x:real) m n. (x zpow m) zpow n = x zpow (m * n)`,
  REWRITE_TAC[FORALL_INT_CASES; INT_MUL_LNEG; INT_MUL_RNEG; INT_NEG_NEG] THEN
  REWRITE_TAC[REAL_ZPOW_POW; REAL_INV_POW; INT_OF_NUM_MUL; REAL_INV_INV] THEN
  REWRITE_TAC[REAL_POW_POW]);;

let REAL_ZPOW_MUL = prove
 (`!(x:real) (y:real) n. (x * y) zpow n = x zpow n * y zpow n`,
  REWRITE_TAC[FORALL_INT_CASES; REAL_ZPOW_POW; REAL_POW_MUL; REAL_INV_MUL]);;

let REAL_ZPOW_DIV = prove
 (`!(x:real) (y:real) n. (x / y) zpow n = x zpow n / y zpow n`,
  REWRITE_TAC[real_div; REAL_INV_ZPOW; REAL_ZPOW_MUL]);;

let REAL_ZPOW_ADD = prove
 (`!(x:real) m n.
        ~(x = &0) ==> x zpow (m + n) = x zpow m * x zpow n`,
  REWRITE_TAC[FORALL_INT_CASES; GSYM INT_NEG_ADD; INT_OF_NUM_ADD] THEN
  REWRITE_TAC[REAL_ZPOW_POW; REAL_POW_ADD; REAL_INV_MUL] THEN
  X_GEN_TAC `x:real` THEN GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
    [REAL_MUL_SYM; INT_ADD_SYM] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EQ_INV2] THEN
    REWRITE_TAC[REAL_INV_MUL; REAL_INV_INV; GSYM REAL_ZPOW_NEG] THEN
    REWRITE_TAC[INT_ARITH `--(--x + y):int = --y + x`] THEN
    REWRITE_TAC[REAL_MUL_AC];
    MAP_EVERY X_GEN_TAC [`n:num`; `p:num`] THEN
    REWRITE_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    SIMP_TAC[GSYM INT_OF_NUM_ADD; ARITH_RULE `--n + (n + m):int = m`] THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_ZPOW_NUM; REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_POW_EQ_0; REAL_MUL_LID]]);;

let REAL_ZPOW_SUB = prove
 (`!(x:real) m n.
        ~(x = &0) ==> x zpow (m - n) = x zpow m / x zpow n`,
  SIMP_TAC[INT_SUB; REAL_ZPOW_ADD; REAL_ZPOW_NEG; real_div]);;

let REAL_ZPOW_LE = prove
 (`!x n. &0 <= x ==> &0 <= x zpow n`,
  SIMP_TAC[FORALL_INT_CASES; REAL_ZPOW_POW; REAL_LE_INV_EQ; REAL_POW_LE]);;

let REAL_ZPOW_LT = prove
 (`!x n. &0 < x ==> &0 < x zpow n`,
  SIMP_TAC[FORALL_INT_CASES; REAL_ZPOW_POW; REAL_LT_INV_EQ; REAL_POW_LT]);;

let REAL_ZPOW_EQ_0 = prove
 (`!x n. x zpow n = &0 <=> x = &0 /\ ~(n = &0)`,
  REWRITE_TAC[FORALL_INT_CASES; REAL_ZPOW_POW; REAL_INV_EQ_0] THEN
  REWRITE_TAC[INT_NEG_EQ_0; REAL_POW_EQ_0; INT_OF_NUM_EQ]);;

let REAL_ABS_ZPOW = prove
 (`!x n. abs(x zpow n) = abs(x) zpow n`,
  REWRITE_TAC[FORALL_INT_CASES; REAL_ZPOW_POW; REAL_ABS_INV; REAL_ABS_POW]);;

let REAL_SGN_ZPOW = prove
 (`!x n. real_sgn(x zpow n) = real_sgn(x) zpow n`,
  REWRITE_TAC[FORALL_INT_CASES; REAL_ZPOW_POW] THEN
  REWRITE_TAC[GSYM REAL_SGN_POW] THEN
  REWRITE_TAC[REAL_SGN_INV; REAL_INV_SGN]);;

(* ------------------------------------------------------------------------- *)
(* Make sure we give priority to N.                                          *)
(* ------------------------------------------------------------------------- *)

prioritize_num();;
