(* ========================================================================= *)
(*          Theory of machine words using finite indexing types.             *)
(*                                                                           *)
(* Introduces a type `:N word` of N-bit words (N being a type of size N).    *)
(* Note that this builds in a priori the assumption the wordsize is nonzero. *)
(* Some abbreviations like `:byte` = `8 word` are often used for brevity.    *)
(*                                                                           *)
(* Mappings `val:N word->num` and `word:num->N word` for unsigned values,    *)
(* and similar 2s-complement `ival:N word->int` and `iword:int->word`, cast  *)
(* (reducing modulo wordsize in one direction) between words and numbers.    *)
(* The `bit` function gives a specific bit as a Boolean.                     *)
(*                                                                           *)
(* The usual operations are provided like `word_add`, `word_xor`; currently  *)
(* for explicitness we don't overload the usual operators. Some have signed  *)
(* and unsigned variants (e.g. `word_ushr` is unsigned/logical shift right,  *)
(* while `word_ishr` is signed/arithmetical shift right).                    *)
(*                                                                           *)
(* For some cases where the result is debatable or machine-dependent, we     *)
(* have versions that match the JVM tagged with a "j" (e.g. `word_jshr`      *)
(* truncates shift counts modulo word size).                                 *)
(*                                                                           *)
(* There are conversions like WORD_REDUCE_CONV for reducing via proof        *)
(* expressions built up from concrete words like `word 255:byte`.            *)
(*                                                                           *)
(* Some simple decision procedures for proving basic word lemmas are here    *)
(* too, and have limited and somewhat complementary scopes:                  *)
(*                                                                           *)
(*  - WORD_RULE for simple algebraic properties                              *)
(*  - WORD_BITWISE_RULE for bitwise-type properties of logical operations    *)
(*  - WORD_ARITH for things involving numerical values                       *)
(*  - WORD_BLAST for fixed-size bitwise expansions followed by arithmetic    *)
(*  - BITBLAST_RULE is a BDD-based "flattening" or "bit-blasting" rule       *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 2019-2024                       *)
(*                (c) Copyright, Mario Carneiro 2020                         *)
(*                (c) Copyright, June Lee 2022-2024                          *)
(* ========================================================================= *)

needs "Library/bdd.ml";;

(* ------------------------------------------------------------------------- *)
(* Some common word sizes.                                                   *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_8 = HAS_SIZE_DIMINDEX_RULE `:8`;;
let HAS_SIZE_16 = HAS_SIZE_DIMINDEX_RULE `:16`;;
let HAS_SIZE_32 = HAS_SIZE_DIMINDEX_RULE `:32`;;
let HAS_SIZE_64 = HAS_SIZE_DIMINDEX_RULE `:64`;;
let HAS_SIZE_128 = HAS_SIZE_DIMINDEX_RULE `:128`;;
let HAS_SIZE_256 = HAS_SIZE_DIMINDEX_RULE `:256`;;
let HAS_SIZE_512 = HAS_SIZE_DIMINDEX_RULE `:512`;;

let DIMINDEX_8 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_8;;
let DIMINDEX_16 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_16;;
let DIMINDEX_32 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_32;;
let DIMINDEX_64 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_64;;
let DIMINDEX_128 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_128;;
let DIMINDEX_256 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_256;;
let DIMINDEX_512 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_512;;

(* ------------------------------------------------------------------------- *)
(* Pre-cache some sizes to speed up computation (only affects efficiency).   *)
(* ------------------------------------------------------------------------- *)

let word_sizes = ref ([]:thm list);;
let word_pow2sizes = ref ([]:thm list);;

let word_SIZE_CONV = ref NO_CONV;;
let word_POW2SIZE_CONV = ref NO_CONV;;

let add_word_sizes =
  let ptm = `(EXP) 2` in
  let sumconv = GEN_REWRITE_CONV I [DIMINDEX_FINITE_SUM] in
  let rec conv tm =
    ((sumconv THENC BINOP_CONV conv THENC NUM_ADD_CONV) ORELSEC
     DIMINDEX_CONV) tm in
  let conv2 tm =
    match tm with
      Comb(t,d) when t = ptm -> (RAND_CONV conv THENC NUM_EXP_CONV) tm
    | _ -> failwith "conv2" in
  let _ = (word_SIZE_CONV := conv; word_POW2SIZE_CONV := conv2) in
  fun l -> let m = !word_sizes
           and m2 = !word_pow2sizes
           and l2 = map (CONV_RULE(RAND_CONV NUM_EXP_CONV) o AP_TERM ptm) l in
           if subset l m then () else
           (word_sizes := union l m;
            word_pow2sizes := union l2 m2;
            word_SIZE_CONV :=
             (GEN_REWRITE_CONV I (!word_sizes) ORELSEC conv);
            word_POW2SIZE_CONV :=
             (GEN_REWRITE_CONV I (!word_pow2sizes) ORELSEC conv2));;

add_word_sizes [DIMINDEX_1; DIMINDEX_2; DIMINDEX_3; DIMINDEX_4];;

add_word_sizes [DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64];;

add_word_sizes [DIMINDEX_128; DIMINDEX_256; DIMINDEX_512];;

(* ------------------------------------------------------------------------- *)
(* Some generic lemmas about digit sums.                                     *)
(* ------------------------------------------------------------------------- *)

let DIGITSUM_WORKS_GEN = prove
 (`!B n k.
    nsum {i | i < k} (\i. B EXP i * n DIV (B EXP i) MOD B) = n MOD (B EXP k)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  SIMP_TAC[NUMSEG_CLAUSES_LT; NSUM_CLAUSES; MOD_1; EXP; FINITE_NUMSEG_LT] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM; LT_REFL] THEN
  MESON_TAC[MOD_MULT_MOD; MULT_SYM]);;

let DIGITSUM_WORKS = prove
 (`!B n k.
        n < B EXP k
        ==> nsum {i | i < k} (\i. B EXP i * n DIV (B EXP i) MOD B) = n`,
  SIMP_TAC[DIGITSUM_WORKS_GEN; MOD_LT]);;

let DIGITSUM_BOUND = prove
 (`!B b k. (!i. i < k ==> b i < B)
           ==> nsum {i | i < k} (\i. B EXP i * b i) < B EXP k`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; EXP; ARITH] THEN
  REWRITE_TAC[LT] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ARITH_RULE
   `s < e /\ e * (x + 1) <= e * b ==> s + e * x < b * e`) THEN
  ASM_SIMP_TAC[LE_MULT_LCANCEL; ARITH_RULE `b + 1 <= c <=> b < c`]);;

let DIGITSUM_SPLIT = prove
 (`!B b s n.
        FINITE s
        ==> B EXP n * nsum {i | i IN s /\ n <= i} (\i. B EXP (i - n) * b i) +
            nsum {i | i IN s /\ i < n} (\i. B EXP i * b i) =
            nsum s (\i. B EXP i * b i)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM NSUM_LMUL; MULT_ASSOC; GSYM EXP_ADD] THEN
  SIMP_TAC[ARITH_RULE `n:num <= i ==> n + i - n = i`] THEN
  MATCH_MP_TAC NSUM_UNION_EQ THEN ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  SET_TAC[]);;

let DIGITSUM_DIV,DIGITSUM_MOD = (CONJ_PAIR o prove)
 (`(!B b s n.
        FINITE s /\ (!i. i IN s ==> b i < B)
        ==> nsum s (\i. B EXP i * b i) DIV (B EXP n) =
            nsum {i | i IN s /\ n <= i} (\i. B EXP (i - n) * b i)) /\
   (!B b s n.
        FINITE s /\ (!i. i IN s ==> b i < B)
        ==> nsum s (\i. B EXP i * b i) MOD (B EXP n) =
            nsum {i | i IN s /\ i < n} (\i. B EXP i * b i))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `B = 0` THENL
   [ASM_REWRITE_TAC[CONJUNCT1 LT; SET_RULE `(!x. ~(x IN s)) <=> s = {}`] THEN
    SIMP_TAC[EMPTY_GSPEC; NOT_IN_EMPTY; CONJUNCT1 NSUM_CLAUSES] THEN
    REWRITE_TAC[DIV_0; MOD_0];
    ALL_TAC] THEN
  REWRITE_TAC[TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  STRIP_TAC THEN MATCH_MP_TAC DIVMOD_UNIQ THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [MULT_SYM] THEN
    MATCH_MP_TAC(GSYM DIGITSUM_SPLIT) THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[SET_RULE
     `{x | x IN s /\ P x} = {x | x IN {y | P y} /\ x IN s}`] THEN
    REWRITE_TAC[NSUM_RESTRICT_SET; MESON[MULT_CLAUSES]
     `(if p then a * b else 0) = a * (if p then b else 0)`] THEN
    MATCH_MP_TAC DIGITSUM_BOUND THEN ASM_MESON_TAC[LE_1]]);;

let DIGITSUM_MOD_NUMSEG = prove
 (`!B b m n.
        (!i. i < m ==> b i < B)
        ==> nsum {i | i < m} (\i. B EXP i * b i) MOD (B EXP n) =
            nsum {i | i < MIN m n} (\i. B EXP i * b i)`,
  SIMP_TAC[DIGITSUM_MOD; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  REWRITE_TAC[ARITH_RULE `i < MIN m n <=> i < m /\ i < n`]);;

let DIGITSUM_DIV_NUMSEG = prove
 (`!B b m n.
        (!i. i < m ==> b i < B)
        ==> nsum {i | i < m} (\i. B EXP i * b i) DIV (B EXP n) =
            nsum {i | i < m - n} (\i. B EXP i * b(i + n))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIGITSUM_DIV; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `{i:num | i < m /\ n <= i} = IMAGE (\i. i + n) {i | i < m - n}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; ARITH_RULE
     `x:num = y + n <=> y = x - n /\ n <= x`] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM2] THEN ARITH_TAC;
    SIMP_TAC[NSUM_IMAGE; EQ_ADD_RCANCEL; o_DEF; ADD_SUB]]);;

let DIGITSUM_DIV_MOD = prove
 (`!B b s n.
        FINITE s /\ (!i. i IN s ==> b i < B)
        ==> nsum s (\i. B EXP i * b i) DIV (B EXP n) MOD B =
            if n IN s then b n else 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DIV_MOD] THEN
  REWRITE_TAC[MESON[EXP; MULT_SYM] `B EXP n * B = B EXP SUC n`] THEN
  ASM_SIMP_TAC[DIGITSUM_MOD] THEN
  ASM_SIMP_TAC[DIGITSUM_DIV; FINITE_RESTRICT; IN_ELIM_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; ARITH_RULE `i < SUC n /\ n <= i <=> i = n`] THEN
  REWRITE_TAC[MESON[] `i IN s /\ i = n <=> n IN s /\ i = n`] THEN
  ASM_CASES_TAC `(n:num) IN s` THEN
  ASM_REWRITE_TAC[EMPTY_GSPEC; NSUM_CLAUSES] THEN
  REWRITE_TAC[SING_GSPEC; NSUM_SING; SUB_REFL; MULT_CLAUSES; EXP]);;

let DIGITSUM_UNIQUE = prove
 (`!B b c s.
     FINITE s /\
     (!i. i IN s ==> b i < B) /\
     (!i. i IN s ==> c i < B)
     ==> (nsum s (\i. B EXP i * b i) = nsum s (\i. B EXP i * c i) <=>
          !i. i IN s ==> b i = c i)`,
  MESON_TAC[DIGITSUM_DIV_MOD; NSUM_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Mapping a Boolean to the natural number 1 (true) or 0 (false)             *)
(* ------------------------------------------------------------------------- *)

let bitval = new_definition
 `bitval b = if b then 1 else 0`;;

let BITVAL_CLAUSES = prove
 (`bitval F = 0 /\ bitval T = 1`,
  REWRITE_TAC[bitval]);;

let BITVAL_BOUND = prove
 (`!b. bitval b <= 1`,
  REWRITE_TAC[bitval] THEN ARITH_TAC);;

let BITVAL_BOUND_ALT = prove
 (`!b. bitval b < 2`,
  REWRITE_TAC[bitval] THEN ARITH_TAC);;

let ODD_BITVAL = prove
 (`!b. ODD(bitval b) <=> b`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES; ARITH]);;

let EVEN_BITVAL = prove
 (`!b. EVEN(bitval b) <=> ~b`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES; ARITH]);;

let NUM_AS_BITVAL = prove
 (`!n. n <= 1 <=> ?b. n = bitval b`,
  REWRITE_TAC[EXISTS_BOOL_THM; BITVAL_CLAUSES] THEN ARITH_TAC);;

let NUM_AS_BITVAL_ALT = prove
 (`!n. n < 2 <=> ?b. n = bitval b`,
  REWRITE_TAC[EXISTS_BOOL_THM; BITVAL_CLAUSES] THEN ARITH_TAC);;

let BITVAL_EQ_0 = prove
 (`!b. bitval b = 0 <=> ~b`,
  GEN_TAC THEN REWRITE_TAC[bitval] THEN
  ASM_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let BITVAL_EQ_1 = prove
 (`!b. bitval b = 1 <=> b`,
  GEN_TAC THEN REWRITE_TAC[bitval] THEN
  ASM_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let BITVAL_POS = prove
 (`!b. 0 < bitval b <=> b`,
  REWRITE_TAC[ARITH_RULE `0 < a <=> ~(a = 0)`; BITVAL_EQ_0]);;

let BITVAL_NOT = prove
 (`!b. bitval(~b) = 1 - bitval b`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let BITVAL_AND = prove
 (`!b c. bitval(b /\ c) = bitval b * bitval c`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let BITVAL_OR = prove
 (`!b c. bitval(b \/ c) = (bitval b + bitval c) - bitval b * bitval c`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let BITVAL_IFF = prove
 (`!b c. bitval(b <=> c) =
         (1 + 2 * bitval b * bitval c) - (bitval b + bitval c)`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let BITVAL_XOR = prove
 (`!b c. bitval(~(b <=> c)) = (bitval b + bitval c) - 2 * bitval b * bitval c`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let BITVAL_EXP = prove
 (`!b k. bitval b EXP k = if k = 0 then 1 else bitval b`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[EXP] THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[EXP_ZERO; EXP_ONE]);;

let INT_BITVAL_NOT = prove
 (`!b. &(bitval(~b)):int = &1 - &(bitval b)`,
  SIMP_TAC[BITVAL_NOT; GSYM INT_OF_NUM_SUB; BITVAL_BOUND]);;

let INT_BITVAL_AND = prove
 (`!b c. &(bitval(b /\ c)):int = &(bitval b) * &(bitval c)`,
  REWRITE_TAC[BITVAL_AND; INT_OF_NUM_CLAUSES]);;

let INT_BITVAL_OR = prove
 (`!b c. &(bitval(b \/ c)):int =
         (&(bitval b) + &(bitval c)) - &(bitval b) * &(bitval c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bitval] THEN
  MAP_EVERY ASM_CASES_TAC [`b:bool`; `c:bool`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN INT_ARITH_TAC);;

let INT_BITVAL_IMP = prove
 (`!b c. &(bitval(b ==> c)):int =
         (&1 - &(bitval b) + &(bitval c)) - (&1 - &(bitval b)) * &(bitval c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bitval] THEN
  MAP_EVERY ASM_CASES_TAC [`b:bool`; `c:bool`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN INT_ARITH_TAC);;

let INT_BITVAL_IFF = prove
 (`!b c. &(bitval(b <=> c)):int =
         &1 - ((&(bitval b) + &(bitval c)) - &2 * &(bitval b) * &(bitval c))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bitval] THEN
  MAP_EVERY ASM_CASES_TAC [`b:bool`; `c:bool`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN INT_ARITH_TAC);;

let INT_BITVAL_POW = prove
 (`!b k. &(bitval b) pow k = if k = 0 then &1:int else &(bitval b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_OF_NUM_CLAUSES; BITVAL_EXP] THEN
  MESON_TAC[]);;

let REAL_BITVAL_NOT = prove
 (`!b. &(bitval(~b)):real = &1 - &(bitval b)`,
  SIMP_TAC[BITVAL_NOT; GSYM REAL_OF_NUM_SUB; BITVAL_BOUND]);;

let BITVAL_ODD = prove
 (`!n. bitval(ODD n) = n MOD 2`,
  REWRITE_TAC[bitval; GSYM NOT_EVEN; MOD_2_CASES; COND_SWAP]);;

let LE_BITVAL = prove
 (`!b c. bitval b <= bitval c <=> b ==> c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bitval] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let INT_LE_BITVAL = prove
 (`!b c. &(bitval b):int <= &(bitval c) <=> b ==> c`,
  REWRITE_TAC[INT_OF_NUM_LE; LE_BITVAL]);;

let REAL_LE_BITVAL = prove
 (`!b c. &(bitval b):real <= &(bitval c) <=> b ==> c`,
  REWRITE_TAC[REAL_OF_NUM_LE; LE_BITVAL]);;

let EQ_BITVAL = prove
 (`!b c. (bitval b = bitval c) <=> (b <=> c)`,
  REWRITE_TAC[GSYM LE_ANTISYM; LE_BITVAL] THEN CONV_TAC TAUT);;

let INT_EQ_BITVAL = prove
 (`!b c. &(bitval b):int = &(bitval c) <=> (b <=> c)`,
  REWRITE_TAC[INT_OF_NUM_EQ; EQ_BITVAL]);;

let REAL_EQ_BITVAL = prove
 (`!b c. &(bitval b):real = &(bitval c) <=> (b <=> c)`,
  REWRITE_TAC[REAL_OF_NUM_EQ; EQ_BITVAL]);;

let BINT_POLY_CONV =
  let bitpow_conv =
    GEN_REWRITE_CONV I [INT_BITVAL_POW] THENC
    RATOR_CONV(LAND_CONV NUM_EQ_CONV) THENC
    GEN_REWRITE_CONV I [COND_CLAUSES] in
  INT_POLY_CONV THENC
  ONCE_DEPTH_CONV bitpow_conv THENC
  INT_POLY_CONV;;

(* ------------------------------------------------------------------------- *)
(* Some more binary-specific lemmas.                                         *)
(* ------------------------------------------------------------------------- *)

let ODD_MOD_POW2 = prove
 (`!n k. ODD(n MOD 2 EXP k) <=> ~(k = 0) /\ ODD n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `k = 0` THEN
  ASM_REWRITE_TAC[MOD_1; EXP; ODD] THEN
  ASM_SIMP_TAC[ODD_MOD_EVEN; EVEN_EXP; ARITH]);;

let BINARY_DIGITSUM_BOUND = prove
 (`!b k. nsum {i | i < k} (\i. 2 EXP i * bitval(b i)) < 2 EXP k`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC DIGITSUM_BOUND THEN
  REWRITE_TAC[BITVAL_BOUND_ALT]);;

let BINARY_DIGITSUM_SPLIT = prove
 (`!b s n.
        FINITE s
        ==> 2 EXP n *
            nsum {i | i IN s /\ n <= i} (\i. 2 EXP (i - n) * bitval(b i)) +
            nsum {i | i IN s /\ i < n} (\i. 2 EXP i * bitval(b i)) =
            nsum s (\i. 2 EXP i * bitval(b i))`,
  MATCH_ACCEPT_TAC DIGITSUM_SPLIT);;

let BINARY_DIGITSUM_DIV = prove
 (`!b s n.
        FINITE s
        ==> nsum s (\i. 2 EXP i * bitval(b i)) DIV (2 EXP n) =
            nsum {i | i IN s /\ n <= i} (\i. 2 EXP (i - n) * bitval(b i))`,
  SIMP_TAC[DIGITSUM_DIV; BITVAL_BOUND_ALT]);;

let BINARY_DIGITSUM_MOD = prove
 (`!b s n.
        FINITE s
        ==> nsum s (\i. 2 EXP i * bitval(b i)) MOD (2 EXP n) =
            nsum {i | i IN s /\ i < n} (\i. 2 EXP i * bitval(b i))`,
  SIMP_TAC[DIGITSUM_MOD; BITVAL_BOUND_ALT]);;

(* ------------------------------------------------------------------------- *)
(* The type "N word" is in bijection with "bool^N"                           *)
(* ------------------------------------------------------------------------- *)

let word_tybij =
  let th = prove (`?x:bool^N. T`,REWRITE_TAC[]) in
  REWRITE_RULE[]
   (new_type_definition "word" ("mk_word","bitvector") th);;

let WORD_EQ_BITVECTOR = prove
 (`!v w:N word. v = w <=> bitvector v = bitvector w`,
  MESON_TAC[word_tybij]);;

(* ------------------------------------------------------------------------- *)
(* Destructors and constructors for the N-bit word type from nums.           *)
(* ------------------------------------------------------------------------- *)

let dest_word_ty ty =
  match ty with
    Tyapp("word",[n]) -> dest_finty n
  | _ -> failwith "dest_word_ty";;

let mk_word_ty n = mk_type("word",[mk_finty n]);;

(* ------------------------------------------------------------------------- *)
(* Set up some specific sizes that we want.                                  *)
(* ------------------------------------------------------------------------- *)

new_type_abbrev("nybble",`:(4)word`);;
new_type_abbrev("byte",`:(8)word`);;
new_type_abbrev("int16",`:(16)word`);;
new_type_abbrev("int32",`:(32)word`);;
new_type_abbrev("int64",`:(64)word`);;
new_type_abbrev("int128",`:(128)word`);;

(* ------------------------------------------------------------------------- *)
(* Individual selection of bits, indexing from 0 as usual.                   *)
(* ------------------------------------------------------------------------- *)

let bit = new_definition
 `bit i (w:N word) =
    if i < dimindex(:N) then (bitvector w)$(i + 1)
    else F`;;

let WORD_EQ_BITS_ALT = prove
 (`!v w:N word. v = w <=> !i. i < dimindex(:N) ==> bit i v = bit i w`,
  REPEAT GEN_TAC THEN SIMP_TAC[WORD_EQ_BITVECTOR; bit; CART_EQ] THEN
  MESON_TAC[ARITH_RULE `i < n ==> 1 <= i + 1 /\ i + 1 <= n`;
            ARITH_RULE `1 <= i /\ i <= n ==> i = (i - 1) + 1 /\ i - 1 < n`]);;

let WORD_EQ_BITS = prove
 (`!v w:N word. v = w <=> !i. bit i v = bit i w`,
  MESON_TAC[bit; WORD_EQ_BITS_ALT]);;

let BIT_TRIVIAL = prove
 (`!w:(N)word i. dimindex(:N) <= i ==> (bit i w <=> F)`,
  SIMP_TAC[GSYM NOT_LT; bit]);;

let BIT_GUARD = prove
 (`!(x:N word) i. bit i x <=> i < dimindex(:N) /\ bit i x`,
  MESON_TAC[NOT_LT; BIT_TRIVIAL]);;

(* ------------------------------------------------------------------------- *)
(* Mappings to and from sets of bits.                                        *)
(* ------------------------------------------------------------------------- *)

let bits_of_word = new_definition
 `bits_of_word (w:N word) = {i | bit i w}`;;

let word_of_bits = new_definition
 `word_of_bits s:N word = mk_word(lambda i. (i - 1) IN s)`;;

let IN_BITS_OF_WORD = prove
 (`!(w:N word) i. i IN bits_of_word w <=> bit i w`,
  REWRITE_TAC[bits_of_word; IN_ELIM_THM]);;

let BIT_WORD_OF_BITS = prove
 (`!s i. bit i (word_of_bits s:N word) <=> i < dimindex(:N) /\ i IN s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bit; word_of_bits] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[word_tybij] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (ARITH_RULE
   `i < n ==> 1 <= i + 1 /\ i + 1 <= n`)) THEN
  ASM_SIMP_TAC[LAMBDA_BETA; ADD_SUB]);;

let WORD_OF_BITS_EQ = prove
 (`!s t. word_of_bits s:N word = word_of_bits t <=>
         !i. i < dimindex(:N) ==> (i IN s <=> i IN t)`,
  SIMP_TAC[WORD_EQ_BITS; BIT_WORD_OF_BITS] THEN MESON_TAC[]);;

let WORD_OF_BITS_OF_WORD = prove
 (`!w:N word. word_of_bits(bits_of_word w) = w`,
  SIMP_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OF_BITS; bits_of_word; IN_ELIM_THM]);;

let BITS_OF_WORD_OF_BITS = prove
 (`!s. bits_of_word(word_of_bits s:N word) = s INTER {i | i < dimindex(:N)}`,
  GEN_TAC THEN REWRITE_TAC[bits_of_word] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; BIT_WORD_OF_BITS] THEN
  CONV_TAC TAUT);;

let BITS_OF_WORD_EQ = prove
 (`!v w:N word. bits_of_word v = bits_of_word w <=> v = w`,
  MESON_TAC[WORD_OF_BITS_OF_WORD]);;

let WORD_OF_BITS = prove
 (`!w:N word. w = word_of_bits {i | bit i w}`,
  REWRITE_TAC[GSYM bits_of_word; WORD_OF_BITS_OF_WORD]);;

let WORD_OF_BITS_ALT = prove
 (`!w:N word. w = word_of_bits {i | i < dimindex(:N) /\ bit i w}`,
  SIMP_TAC[WORD_EQ_BITS; BIT_WORD_OF_BITS; IN_ELIM_THM] THEN
  MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let FINITE_BITS_OF_WORD = prove
 (`!w:N word. FINITE(bits_of_word w)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{i | i < dimindex(:N)}` THEN
  REWRITE_TAC[bits_of_word; FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[BIT_TRIVIAL; NOT_LT]);;

let BITS_OF_WORD_SUBSET = prove
 (`!(x:M word) (y:N word).
        bits_of_word x SUBSET bits_of_word y <=> !i. bit i x ==> bit i y`,
  REWRITE_TAC[SUBSET; IN_BITS_OF_WORD]);;

let BITS_OF_WORD_SUBSET_ALT = prove
 (`!(x:M word) (y:N word).
        bits_of_word x SUBSET bits_of_word y <=>
        !i. i < dimindex(:M) /\ bit i x ==> bit i y`,
  REWRITE_TAC[GSYM BIT_GUARD; BITS_OF_WORD_SUBSET]);;

let BITS_OF_WORD_SUBSET_NUMSEG = prove
 (`!x:N word. bits_of_word x SUBSET {i | i < dimindex(:N)}`,
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_BITS_OF_WORD] THEN
  MESON_TAC[BIT_GUARD]);;

(* ------------------------------------------------------------------------- *)
(* Mapping to and from natural number values (treating as unsigned word).    *)
(* ------------------------------------------------------------------------- *)

let val_def = new_definition
 `val (w:N word) =
    nsum {i | i < dimindex(:N)} (\i. 2 EXP i * bitval(bit i w))`;;

let VAL = prove
 (`!x:N word.
       val(x) = nsum(0..dimindex(:N)-1) (\i. 2 EXP i * bitval(bit i x))`,
  REWRITE_TAC[val_def; NUMSEG_LT; DIMINDEX_NONZERO]);;

let word = new_definition
 `(word:num->N word) n =
    mk_word(lambda i. ODD(n DIV (2 EXP (i - 1))))`;;

let BIT_WORD = prove
 (`!i n. bit i (word n:N word) <=> i < dimindex(:N) /\ ODD(n DIV (2 EXP i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bit] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[word; word_tybij] THEN
  ASM_SIMP_TAC[LAMBDA_BETA; ADD_SUB; ARITH_RULE `1 <= i + 1`;
               ARITH_RULE `i < n ==> i + 1 <= n`]);;

let BIT_LSB_WORD = prove
 (`!n. bit 0 (word n) <=> ODD n`,
  SIMP_TAC[BIT_WORD; DIV_1; EXP; DIMINDEX_GE_1; LE_1]);;

let BIT_WORD_0 = prove
 (`!i. bit i (word 0:N word) <=> F`,
  REWRITE_TAC[BIT_WORD; DIV_0; ODD]);;

let BITS_OF_WORD_0 = prove
 (`bits_of_word(word 0:N word) = {}`,
  REWRITE_TAC[bits_of_word; BIT_WORD_0; EMPTY_GSPEC]);;

let BITS_OF_WORD_EQ_EMPTY = prove
 (`!w:N word. bits_of_word w = {} <=> w = word 0`,
  REWRITE_TAC[GSYM BITS_OF_WORD_EQ; BITS_OF_WORD_0]);;

let WORD_OF_BITS_EMPTY = prove
 (`word_of_bits {}:N word = word 0`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_0; BIT_WORD_OF_BITS] THEN
  REWRITE_TAC[NOT_IN_EMPTY]);;

let BITVAL_BIT_WORD = prove
 (`!i n. bitval(bit i (word n:N word)) =
         if i < dimindex(:N) then (n DIV (2 EXP i)) MOD 2 else 0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[BIT_WORD; bitval; ODD_MOD] THEN
  ARITH_TAC);;

let WORD_VAL = prove
 (`!w:N word. word(val w) = w`,
  GEN_TAC THEN SIMP_TAC[WORD_EQ_BITS_ALT; val_def; BIT_WORD] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SIMP_TAC[BINARY_DIGITSUM_DIV; FINITE_NUMSEG_LT] THEN
  ASM_SIMP_TAC[IN_ELIM_THM; GSYM numseg; ARITH_RULE
   `k < n ==> (i < n /\ k <= i <=> k <= i /\ i <= n - 1)`] THEN
  ASM_SIMP_TAC[NSUM_CLAUSES_LEFT; ARITH_RULE `k < n ==> k <= n - 1`] THEN
  MATCH_MP_TAC(MESON[ODD; ODD_ADD]
   `~ODD n /\ (ODD m <=> p) ==> (ODD(m + n) <=> p)`) THEN
  REWRITE_TAC[SUB_REFL; EXP; NOT_ODD; MULT_CLAUSES] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_CLOSED THEN
    SIMP_TAC[EVEN; EVEN_ADD; EVEN_MULT; EVEN_EXP; IN_NUMSEG] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]);;

let VAL_WORD = prove
 (`!n. val(word n:N word) = n MOD (2 EXP (dimindex(:N)))`,
  GEN_TAC THEN SIMP_TAC[val_def; BITVAL_BIT_WORD] THEN
  SPEC_TAC(`dimindex(:N)`,`k:num`) THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; EXP; MOD_1] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MOD_MULT_MOD] THEN ARITH_TAC);;

let MOD_VAL_WORD = prove
 (`!n k. k <= dimindex(:N) ==> val(word n:N word) MOD 2 EXP k = n MOD 2 EXP k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= n ==> MIN n k = k`]);;

let DIVIDES_VAL_WORD = prove
 (`!n x. n <= dimindex(:N)
         ==> (2 EXP n divides val(word x:N word) <=> 2 EXP n divides x)`,
  SIMP_TAC[MOD_VAL_WORD; DIVIDES_MOD]);;

let VAL_WORD_LE = prove
 (`!n k. n <= k ==> val(word n:N word) <= k`,
  REWRITE_TAC[VAL_WORD] THEN MESON_TAC[LE_TRANS; MOD_LE]);;

let VAL_WORD_LT = prove
 (`!n k. n < k ==> val(word n:N word) < k`,
  REWRITE_TAC[VAL_WORD] THEN MESON_TAC[LET_TRANS; MOD_LE]);;

let FORALL_WORD = prove
 (`!P. (!x:N word. P x) <=> (!n. P(word n))`,
  MESON_TAC[WORD_VAL]);;

let EXISTS_WORD = prove
 (`!P. (?x:N word. P x) <=> (?n. P(word n))`,
  MESON_TAC[WORD_VAL]);;

let VAL_WORD_0 = prove
 (`val(word 0:(N)word) = 0`,
  SIMP_TAC[VAL_WORD; MOD_0; EXP_EQ_0; ARITH_EQ]);;

let VAL_WORD_1 = prove
 (`val(word 1:(N)word) = 1`,
  REWRITE_TAC[VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `1 = 2 EXP 0`] THEN
  SIMP_TAC[LT_EXP; LE_1; DIMINDEX_GE_1] THEN ARITH_TAC);;

let WORD_BITVAL = prove
 (`!b. word(bitval b) = if b then word 1 else word 0`,
  REWRITE_TAC[bitval] THEN MESON_TAC[]);;

let VAL_WORD_BITVAL = prove
 (`!b. val(word(bitval b)) = bitval b`,
  MATCH_MP_TAC bool_INDUCT THEN
  REWRITE_TAC[VAL_WORD_1; VAL_WORD_0; BITVAL_CLAUSES]);;

let VAL_WORD_EQ = prove
 (`!n. n < 2 EXP dimindex(:N) ==> val(word n :(N)word) = n`,
  SIMP_TAC[VAL_WORD; MOD_LT]);;

let VAL_EQ = prove
 (`!(v:N word) (w:N word). val v = val w <=> v = w`,
  MESON_TAC[WORD_VAL]);;

let VAL_EQ_0 = prove
 (`!w:(N)word. val w = 0 <=> w = word 0`,
  MESON_TAC[VAL_WORD_0; VAL_EQ]);;

let VAL_EQ_1 = prove
 (`!w:(N)word. val w = 1 <=> w = word 1`,
  MESON_TAC[VAL_WORD_1; VAL_EQ]);;

let VAL_EQ_BITVAL = prove
 (`!w:(N)word b. val w = bitval b <=> w = word(bitval b)`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES; VAL_EQ_0; VAL_EQ_1]);;

let WORD_BITVAL_EQ_0 = prove
 (`!b. word(bitval b):N word = word 0 <=> ~b`,
  REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_BITVAL; BITVAL_EQ_0]);;

let WORD_BITVAL_EQ_1 = prove
 (`!b. word(bitval b):N word = word 1 <=> b`,
  REWRITE_TAC[GSYM VAL_EQ_1; VAL_WORD_BITVAL; BITVAL_EQ_1]);;

let WORD_NE_10 = prove
 (`~(word 1:N word = word 0)`,
  REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_1] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_EQ = prove
 (`!x y. word x:(N)word = word y <=> (x == y) (mod (2 EXP dimindex(:N)))`,
  MESON_TAC[VAL_WORD; WORD_VAL; CONG]);;

let WORD_EQ_IMP = prove
 (`!m n. m < 2 EXP dimindex(:N) /\ n < 2 EXP dimindex(:N)
         ==> (word m:N word = word n <=> m = n)`,
  REWRITE_TAC[WORD_EQ; CONG] THEN SIMP_TAC[MOD_LT]);;

let WORD_EQ_0 = prove
 (`!m. m < 2 EXP dimindex(:N) ==> (word m:N word = word 0 <=> m = 0)`,
  SIMP_TAC[WORD_EQ_IMP; EXP_LT_0; ARITH_EQ]);;

let VAL_BOUND = prove
 (`!w:N word. val w < 2 EXP dimindex(:N)`,
  REWRITE_TAC[val_def; BINARY_DIGITSUM_BOUND]);;

let INT_VAL_BOUND = prove
 (`!w:N word. &(val w):int < &2 pow dimindex(:N)`,
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LT; VAL_BOUND]);;

let VAL_MOD_REFL = prove
 (`!x:(N)word. (val x) MOD (2 EXP dimindex(:N)) = val x`,
  MESON_TAC[MOD_LT; VAL_BOUND]);;

let VAL_WORD_EQ_EQ = prove
 (`!n. val(word n:N word) = n <=> n < 2 EXP dimindex(:N)`,
  MESON_TAC[VAL_WORD_EQ; VAL_BOUND]);;

let FORALL_VAL_GEN = prove
 (`!P. (!x:N word. P (val x) x) <=>
       !n. n < 2 EXP dimindex(:N) ==> P n (word n)`,
  MESON_TAC[VAL_WORD_EQ; WORD_VAL; VAL_BOUND]);;

let FORALL_VAL = prove
 (`!P. (!x:N word. P(val x)) <=> (!n. n < 2 EXP dimindex(:N) ==> P n)`,
  REWRITE_TAC[FORALL_VAL_GEN]);;

let VAL_CONG = prove
 (`!(v:N word) (w:N word).
        (val v == val w) (mod (2 EXP dimindex(:N))) <=> v = w`,
  REWRITE_TAC[GSYM VAL_EQ; CONG; MOD_MOD_REFL; VAL_MOD_REFL]);;

let WORD_MOD_SIZE = prove
 (`!n. word(n MOD (2 EXP dimindex(:N))):N word = word n`,
  REWRITE_TAC[WORD_EQ; CONG; MOD_MOD_REFL]);;

let VAL_WORD_CONG = prove
 (`!x. (val(word x:N word) == x) (mod (2 EXP (dimindex(:N))))`,
  REWRITE_TAC[VAL_WORD; CONG; MOD_MOD_REFL]);;

let VAL_WORD_GALOIS = prove
 (`!(w:N word) n. val w = n <=> n < 2 EXP dimindex(:N) /\ w = word n`,
  MESON_TAC[WORD_VAL; VAL_WORD_EQ; VAL_BOUND]);;

let WORD_VAL_GALOIS = prove
 (`!(w:N word) n. word n = w <=> n MOD 2 EXP dimindex(:N) = val w`,
  MESON_TAC[VAL_WORD; WORD_MOD_SIZE; WORD_VAL]);;

let DIVIDES_VAL_WORD_EQ = prove
 (`!n x. 2 EXP n divides val(word x:N word) <=>
         if n < dimindex(:N) then 2 EXP n divides x
         else word x:N word = word 0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[DIVIDES_VAL_WORD; LT_IMP_LE] THEN
  EQ_TAC THEN SIMP_TAC[VAL_WORD_0; NUMBER_RULE `n divides 0`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  REWRITE_TAC[VAL_EQ_0] THEN MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN
  REWRITE_TAC[NOT_LE] THEN TRANS_TAC LTE_TRANS `2 EXP dimindex(:N)` THEN
  REWRITE_TAC[VAL_BOUND; LE_EXP] THEN ASM_ARITH_TAC);;

let BIT_VAL = prove
 (`!(x:N word) i. bit i x <=> ODD(val x DIV (2 EXP i))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM WORD_VAL] THEN
  REWRITE_TAC[BIT_WORD; TAUT `(p /\ q <=> q) <=> (~p ==> ~q)`] THEN
  REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
  MATCH_MP_TAC(MESON[ODD] `n = 0 ==> ~ODD n`) THEN
  ASM_SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  TRANS_TAC LTE_TRANS `2 EXP dimindex(:N)` THEN
  ASM_REWRITE_TAC[VAL_BOUND; LE_EXP; DIMINDEX_NONZERO; COND_ID]);;

let BIT_VAL_MOD = prove
 (`!(x:N word) k.
        bit k x <=> 2 EXP k <= val(x) MOD 2 EXP (k + 1)`,
  REWRITE_TAC[BIT_VAL; GSYM NOT_EVEN; EVEN_MOD; EXP_ADD; EXP_1; DIV_MOD] THEN
  SIMP_TAC[DIV_EQ_0; NOT_LT; EXP_EQ_0; ARITH_EQ]);;

let BIT_LSB = prove
 (`!x:N word. bit 0 x <=> ODD(val x)`,
  REWRITE_TAC[BIT_VAL; EXP; DIV_1]);;

let TWICE_MSB = prove
 (`2 EXP dimindex(:N) = 2 * 2 EXP (dimindex(:N) - 1) /\
   (&2:int) pow dimindex(:N) = &2 * &2 pow (dimindex(:N) - 1)`,
  REWRITE_TAC[GSYM(CONJUNCT2 EXP); GSYM(CONJUNCT2 INT_POW)] THEN
  SIMP_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> SUC(n - 1) = n`]);;

let MSB_VAL = prove
 (`!w:N word. bit (dimindex(:N) - 1) w <=> 2 EXP (dimindex(:N) - 1) <= val w`,
  SIMP_TAC[BIT_VAL_MOD; SUB_ADD; DIMINDEX_GE_1; VAL_MOD_REFL]);;

let MSB_INT_VAL = prove
 (`!w:N word.
    bit (dimindex(:N) - 1) w <=> (&2 pow (dimindex(:N) - 1)):int <= &(val w)`,
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LE; MSB_VAL]);;

let BITVAL_MSB = prove
 (`!x:N word. bitval(bit (dimindex(:N)-1) x) =
              val x DIV 2 EXP (dimindex(:N)-1)`,
  GEN_TAC THEN REWRITE_TAC[MSB_VAL] THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `n < 2 /\ ~(n = 0) ==> n = 1`); ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ; RDIV_LT_EQ] THEN
  ASM_REWRITE_TAC[GSYM NOT_LE] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  SIMP_TAC[GSYM(CONJUNCT2 EXP); NOT_LE] THEN
  SIMP_TAC[DIMINDEX_NONZERO; ARITH_RULE `~(n = 0) ==> SUC(n - 1) = n`] THEN
  REWRITE_TAC[VAL_BOUND]);;

let BLOCK_BITS_ZERO_ALT = prove
 (`!(x:N word) m n.
        (!i. m <= i /\ i < n ==> ~bit i x) <=>
        (val x MOD 2 EXP n) DIV 2 EXP m = 0`,
  SIMP_TAC[val_def; BINARY_DIGITSUM_DIV; BINARY_DIGITSUM_MOD;
           FINITE_NUMSEG_LT; FINITE_RESTRICT; NSUM_EQ_0_IFF] THEN
  REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH_EQ; BITVAL_EQ_0; IN_ELIM_THM] THEN
  MESON_TAC[NOT_LT; BIT_TRIVIAL]);;

let BLOCK_BITS_ZERO = prove
 (`!(x:N word) m n.
        (!i. m <= i /\ i < n ==> ~bit i x) <=>
        val x MOD 2 EXP n < 2 EXP m`,
  SIMP_TAC[BLOCK_BITS_ZERO_ALT; DIV_EQ_0; EXP_EQ_0; ARITH_EQ]);;

let LOWER_BITS_ZERO = prove
 (`!(x:N word) n. (!i. i < n ==> ~bit i x) <=> val x MOD 2 EXP n = 0`,
  ONCE_REWRITE_TAC[ARITH_RULE `i < n <=> 0 <= i /\ i < n`] THEN
  REWRITE_TAC[BLOCK_BITS_ZERO_ALT; EXP; DIV_1]);;

let UPPER_BITS_ZERO = prove
 (`!(x:N word) n. (!i. n <= i ==> ~bit i x) <=> val x < 2 EXP n`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL
   [`x:N word`; `n:num`; `dimindex(:N)`] BLOCK_BITS_ZERO) THEN
  REWRITE_TAC[VAL_MOD_REFL] THEN MESON_TAC[NOT_LT; BIT_TRIVIAL]);;

let UPPER_BITS_ZERO_ALT = prove
 (`!(x:N word) n. (!i. n <= i ==> ~bit i x) <=> val x DIV 2 EXP n = 0`,
  SIMP_TAC[UPPER_BITS_ZERO; DIV_EQ_0; EXP_EQ_0; ARITH_EQ]);;

let VAL_WORD_OF_BITS = prove
 (`!s. val(word_of_bits s:N word) =
       nsum {i | i < dimindex(:N) /\ i IN s} (\i. 2 EXP i)`,
  GEN_TAC THEN SIMP_TAC[val_def; BIT_WORD_OF_BITS; bitval] THEN
  REWRITE_TAC[COND_RAND; MULT_CLAUSES; GSYM NSUM_RESTRICT_SET] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let WORD_OF_BITS_AS_WORD = prove
 (`!s. word_of_bits s:N word =
       word(nsum {i | i < dimindex(:N) /\ i IN s} (\i. 2 EXP i))`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_OF_BITS; VAL_WORD] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[GSYM VAL_WORD_OF_BITS; VAL_BOUND]);;

let WORD_OF_BITS_AS_WORD_FINITE = prove
 (`!s. FINITE s ==> word_of_bits s:N word = word(nsum s (\i. 2 EXP i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ; WORD_OF_BITS_AS_WORD] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[NSUM_RESTRICT_SET] THEN
  MATCH_MP_TAC CONG_NSUM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[NUMBER_RULE `(n:num == n) (mod p)`] THEN
  REWRITE_TAC[NUMBER_RULE `(0 == n) (mod p) <=> p divides n`] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LT]) THEN
  SIMP_TAC[LE_EXISTS; EXP_ADD; LEFT_IMP_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN CONV_TAC NUMBER_RULE);;

let WORD_OF_BITS_SING_AS_WORD = prove
 (`!i. word_of_bits {i}:N word = word(2 EXP i)`,
  SIMP_TAC[WORD_OF_BITS_AS_WORD_FINITE; FINITE_SING; NSUM_SING]);;

let VAL_WORD_OF_BITS_SING = prove
 (`!i. val(word_of_bits {i}:N word) = if i < dimindex(:N) then 2 EXP i else 0`,
  GEN_TAC THEN SIMP_TAC[val_def; BIT_WORD_OF_BITS; IN_SING; bitval] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [COND_RAND] THEN
  SIMP_TAC[MULT_CLAUSES; NSUM_DELTA; IN_ELIM_THM]);;

let WORD_OF_BITS_MASK = prove
 (`!n. word_of_bits {i | i < n}:N word = word(2 EXP n - 1)`,
  GEN_TAC THEN SIMP_TAC[WORD_OF_BITS_AS_WORD_FINITE; FINITE_NUMSEG_LT] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC(ARITH_RULE `n + 1 = m ==> n = m - 1`) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; EXP] THEN
  ASM_ARITH_TAC);;

let BIT_MASK_WORD = prove
 (`!k i. bit i (word(2 EXP k - 1):N word) <=> i < dimindex(:N) /\ i < k`,
  REWRITE_TAC[GSYM WORD_OF_BITS_MASK; IN_ELIM_THM; BIT_WORD_OF_BITS]);;

let BIT_WORD_POW2 = prove
 (`!k i. bit i (word (2 EXP k):N word) <=> i = k /\ k < dimindex(:N)`,
  REWRITE_TAC[GSYM WORD_OF_BITS_SING_AS_WORD; BIT_WORD_OF_BITS] THEN
  SET_TAC[]);;

let BIT_WORD_1 = prove
 (`!i. bit i (word 1:N word) <=> i = 0`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `1 = 2 EXP 0`] THEN
  SIMP_TAC[BIT_WORD_POW2; LE_1; DIMINDEX_GE_1]);;

let BIT_WORD_BITVAL = prove
 (`!b i. bit i (word(bitval b):N word) <=> i = 0 /\ b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bitval] THEN
  COND_CASES_TAC THEN REWRITE_TAC[BIT_WORD_0; BIT_WORD_1]);;

let WORD_OF_BITS_SING_AS_WORD_1 = prove
 (`word_of_bits {0}:N word = word 1`,
  REWRITE_TAC[WORD_OF_BITS_SING_AS_WORD; EXP]);;

let BITS_OF_WORD_1 = prove
 (`bits_of_word (word 1:N word) = {0}`,
  REWRITE_TAC[bits_of_word; BIT_WORD_1] THEN SET_TAC[]);;

let BIT_WORD_OF_BITS_SING = prove
 (`!k i. bit i (word_of_bits {k}:N word) <=> k < dimindex(:N) /\ i = k`,
  REWRITE_TAC[BIT_WORD_OF_BITS; IN_SING] THEN MESON_TAC[]);;

let VAL_MOD = prove
 (`!(x:N word) k.
        val x MOD 2 EXP k = nsum {i | i < k} (\i. 2 EXP i * bitval(bit i x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[val_def] THEN
  SIMP_TAC[BINARY_DIGITSUM_MOD; FINITE_NUMSEG_LT] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_SUPERSET THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; IMP_CONJ; MULT_EQ_0; BITVAL_EQ_0; NOT_LT] THEN
  MESON_TAC[BIT_TRIVIAL]);;

let VAL_MOD_2 = prove
 (`!x:N word. val x MOD 2 = bitval(bit 0 x)`,
  ONCE_REWRITE_TAC[ARITH_RULE `2 = 2 EXP 1`] THEN
  REWRITE_TAC[VAL_MOD; ARITH_RULE `i < 1 <=> i = 0`; SING_GSPEC] THEN
  REWRITE_TAC[NSUM_SING; EXP; MULT_CLAUSES]);;

let VAL_MOD_STEP = prove
 (`!(x:N word) k.
      val x MOD 2 EXP (k + 1) = 2 EXP k * bitval(bit k x) + val x MOD 2 EXP k`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_MOD; ARITH_RULE `i < k + 1 <=> i = k \/ i < k`] THEN
  REWRITE_TAC[SET_RULE `{x | x = a \/ P x} = a INSERT {x | P x}`] THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL]);;

let VAL_DIV = prove
 (`!(x:N word) k.
        val x DIV 2 EXP k =
        nsum {i | k <= i /\ i < dimindex(:N)}
             (\i. 2 EXP (i - k) * bitval(bit i x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[val_def] THEN
  SIMP_TAC[BINARY_DIGITSUM_DIV; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REWRITE_TAC[CONJ_SYM]);;

let VAL_DIV_ALT = prove
 (`!(x:N word) k.
        val x DIV 2 EXP k =
        nsum {i | i < dimindex(:N) - k}
             (\i. 2 EXP i * bitval(bit (i + k) x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_DIV] THEN
  MATCH_MP_TAC NSUM_EQ_GENERAL_INVERSES THEN
  EXISTS_TAC `\i:num. i - k` THEN
  EXISTS_TAC `\i:num. i + k` THEN
  SIMP_TAC[IN_ELIM_THM; SUB_ADD] THEN ARITH_TAC);;

let VAL_LE_BITS = prove
 (`!(x:N word) (y:N word).
        (!i. i < dimindex(:N) /\ bit i x ==> bit i y)
        ==> val x <= val y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[val_def] THEN
  MATCH_MP_TAC NSUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[LE_MULT_LCANCEL; LE_BITVAL]);;

let VAL_LE_SUBSET = prove
 (`!(x:N word) (y:N word).
        bits_of_word x SUBSET bits_of_word y ==> val x <= val y`,
  REWRITE_TAC[BITS_OF_WORD_SUBSET_ALT; VAL_LE_BITS]);;

(* ------------------------------------------------------------------------- *)
(* Corresponding signed 2s-complement mappings to and from integers.         *)
(* ------------------------------------------------------------------------- *)

let ival = new_definition
 `(ival:N word->int) w =
    if val(w) < 2 EXP (dimindex(:N) - 1) then &(val w)
    else &(val w) - &2 pow dimindex(:N)`;;

let iword = new_definition
 `(iword:int->N word) x = word(num_of_int(x rem (&2 pow dimindex(:N))))`;;

let word_sgn = new_definition
 `word_sgn (x:N word) = int_sgn(ival x)`;;

let INT_IVAL = prove
 (`!w:N word.
        ival w =
        if &(val w):int < &2 pow (dimindex(:N) - 1) then &(val w)
        else &(val w) - &2 pow dimindex(:N)`,
  REWRITE_TAC[ival; INT_OF_NUM_POW; INT_OF_NUM_LT]);;

let WORD_IWORD = prove
 (`!n. word n:N word = iword(&n)`,
  GEN_TAC THEN REWRITE_TAC[iword; WORD_EQ] THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_REM; NUM_OF_INT_OF_NUM] THEN
  REWRITE_TAC[CONG; MOD_MOD_REFL]);;

let IVAL_VAL = prove
 (`!w:N word.
    ival w =
    &(val w) - &2 pow dimindex(:N) * &(bitval(bit (dimindex(:N) - 1) w))`,
  GEN_TAC THEN REWRITE_TAC[ival; GSYM NOT_LE; GSYM MSB_VAL; COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[bitval] THEN INT_ARITH_TAC);;

let VAL_IVAL = prove
 (`!w:N word.
    &(val w) =
    ival w + &2 pow dimindex(:N) * &(bitval (bit (dimindex (:N) - 1) w))`,
  REWRITE_TAC[IVAL_VAL] THEN CONV_TAC INT_ARITH);;

let IVAL_EQ_VAL = prove
 (`!x:N word. val(x) < 2 EXP (dimindex(:N)-1) ==> ival x = &(val x)`,
  SIMP_TAC[ival]);;

let INT_VAL_IWORD = prove
 (`!x. &0 <= x /\ x < &2 pow dimindex(:N) ==> &(val(iword x:N word)) = x`,
  SIMP_TAC[IMP_CONJ; GSYM INT_FORALL_POS] THEN
  REWRITE_TAC[GSYM WORD_IWORD; INT_OF_NUM_CLAUSES; VAL_WORD_EQ]);;

let INT_VAL_IWORD_EQ = prove
 (`!x. &(val(iword x:N word)) = x <=>
       &0 <= x /\ x < &2 pow dimindex(:N)`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[INT_VAL_IWORD] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; LE_0; VAL_BOUND]);;

let MSB_IVAL = prove
 (`!(w:N word).
        bit (dimindex(:N) - 1) w <=> ival w < &0`,
  GEN_TAC THEN REWRITE_TAC[ival; MSB_VAL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  REWRITE_TAC[INT_NOT_LT; INT_OF_NUM_LE; LE_0] THEN
  REWRITE_TAC[INT_ARITH `a - b:int < &0 <=> a < b`] THEN
  REWRITE_TAC[INT_OF_NUM_LT; INT_OF_NUM_POW; VAL_BOUND]);;

let IVAL_BOUND = prove
 (`!w:(N)word.
        --(&2 pow (dimindex(:N) - 1)) <= ival w /\
        ival w < &2 pow (dimindex(:N) - 1)`,
  GEN_TAC THEN MP_TAC(ISPEC `w:N word` VAL_BOUND) THEN
  REWRITE_TAC[ival; GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_POW] THEN
  SUBGOAL_THEN `?n. dimindex(:N) = SUC n` (CHOOSE_THEN SUBST1_TAC) THENL
   [MESON_TAC[DIMINDEX_NONZERO; num_CASES]; ALL_TAC] THEN
  REWRITE_TAC[SUC_SUB1; INT_POW] THEN INT_ARITH_TAC);;

let IVAL_WORD_0 = prove
 (`ival(word 0) = &0`,
  REWRITE_TAC[ival; VAL_WORD_0; EXP_LT_0] THEN CONV_TAC NUM_REDUCE_CONV);;

let IVAL_WORD_1 = prove
 (`ival(word 1:N word) = if dimindex(:N) = 1 then -- &1 else &1`,
  REWRITE_TAC[ival; VAL_WORD_1] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `1 < x <=> 2 EXP 1 <= x`] THEN
  REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIMINDEX_NONZERO; ARITH_RULE
   `1 <= n - 1 <=> ~(n = 0 \/ n = 1)`] THEN
  ASM_CASES_TAC `dimindex(:N) = 1` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC INT_REDUCE_CONV);;

let IVAL_VAL_CONG = prove
 (`!(w:N word). (ival w == &(val w)) (mod (&2 pow (dimindex(:N))))`,
  GEN_TAC THEN REWRITE_TAC[ival] THEN COND_CASES_TAC THEN
  CONV_TAC INTEGER_RULE);;

let IVAL_CONG = prove
 (`!(v:N word) (w:N word).
      (ival v == ival w) (mod (&2 pow (dimindex(:N)))) <=> v = w`,
  REWRITE_TAC[GSYM VAL_CONG; num_congruent; GSYM INT_OF_NUM_POW] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC(INTEGER_RULE
   `(x:int == x') (mod n) /\ (y == y') (mod n)
    ==> ((x == y) (mod n) <=> (x' == y') (mod n))`) THEN
  REWRITE_TAC[IVAL_VAL_CONG]);;

let IVAL_EQ = prove
 (`!(v:N word) (w:N word). ival v = ival w <=> v = w`,
  MESON_TAC[NUMBER_RULE `(x:int == x) (mod n)`; IVAL_CONG]);;

let IVAL_EQ_0 = prove
 (`!(w:N word). ival w = &0 <=> w = word 0`,
  REWRITE_TAC[GSYM IVAL_EQ; IVAL_WORD_0]);;

let IVAL_EQ_1 = prove
 (`!w:N word. ival w = &1 <=> 2 <= dimindex(:N) /\ w = word 1`,
  GEN_TAC THEN REWRITE_TAC[GSYM IVAL_EQ; IVAL_WORD_1] THEN
  SIMP_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> (2 <= n <=> ~(n = 1))`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `w:N word` IVAL_BOUND) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV);;

let IWORD_EQ = prove
 (`!x y. iword x:N word = iword y <=> (x == y) (mod (&2 pow (dimindex(:N))))`,
  REWRITE_TAC[iword; WORD_EQ; num_congruent; GSYM INT_OF_NUM_POW] THEN
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_DIVISION; INT_POW_EQ_0;
           INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[GSYM INT_REM_EQ; INT_REM_REM]);;

let IWORD_REM_SIZE = prove
 (`!n. iword(n rem (&2 pow dimindex(:N))):N word = iword n`,
  REWRITE_TAC[IWORD_EQ; INT_REM_MOD_SELF]);;

let IVAL_IWORD_CONG = prove
 (`!x. (ival(iword x:N word) == x) (mod (&2 pow (dimindex(:N))))`,
  GEN_TAC THEN MP_TAC(SPEC `iword x:N word` IVAL_VAL_CONG) THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(y:int == z) (mod n) ==> (x == y) (mod n) ==> (x == z) (mod n)`) THEN
  REWRITE_TAC[iword] THEN MATCH_MP_TAC(INTEGER_RULE
   `(&(val(word w:N word)):int == &w) (mod n) /\ (&w:int == z) (mod n)
    ==> (&(val(word w:N word)) == z) (mod n)`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_POW; GSYM num_congruent] THEN
    REWRITE_TAC[VAL_WORD; CONG; MOD_MOD_REFL];
    SIMP_TAC[INT_OF_NUM_OF_INT; INT_DIVISION; INT_POW_EQ_0;
           INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[GSYM INT_REM_EQ; INT_REM_REM]]);;

let VAL_IWORD_CONG = prove
 (`!x. (&(val(iword x:N word)) == x) (mod (&2 pow dimindex(:N)))`,
  REWRITE_TAC[GSYM INT_REM_EQ] THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[GSYM INT_REM_EQ] IVAL_VAL_CONG)] THEN
  REWRITE_TAC[INT_REM_EQ; IVAL_IWORD_CONG]);;

let IVAL_WORD_CONG = prove
 (`!n. (ival(word n:N word) == &n) (mod (&2 pow dimindex(:N)))`,
  MESON_TAC[IVAL_VAL_CONG; VAL_WORD_CONG; INT_OF_NUM_POW; num_congruent;
            INTEGER_RULE `(x:int == y) (mod n) /\ (y == z) (mod n)
                          ==> (x == z) (mod n)`]);;

let IVAL_IWORD = prove
 (`!n. --(&2 pow (dimindex (:N) - 1)) <= n /\ n < &2 pow (dimindex (:N) - 1)
       ==> ival(iword n:N word) = n`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `n:int` IVAL_IWORD_CONG) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] INT_CONG_IMP_EQ) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
   `n:int < e1
    ==> --e1 <= n /\ --e1 <= n' /\ n' < e1 /\ &2 * e1 = e
        ==> abs(n' - n) < e`)) THEN
  ASM_REWRITE_TAC[IVAL_BOUND; GSYM(CONJUNCT2 INT_POW)] THEN
  SIMP_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> SUC(n - 1) = n`]);;

let IWORD_IVAL = prove
 (`!w:N word. iword(ival w) = w`,
  REWRITE_TAC[GSYM IVAL_CONG; IVAL_IWORD_CONG]);;

let IVAL_IWORD_GALOIS = prove
 (`!(w:N word) n.
        ival w = n <=>
        --(&2 pow (dimindex(:N) - 1)) <= n /\
        n < &2 pow (dimindex(:N) - 1) /\
        w = iword n`,
  MESON_TAC[IVAL_IWORD; IWORD_IVAL; IVAL_BOUND]);;

let BIT_IVAL = prove
 (`!(x:N word) i.
    bit i x <=> i < dimindex(:N) /\ ~(&2 divides (ival x div &2 pow i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIT_VAL] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[GSYM NOT_EVEN; EVEN_EXISTS; GSYM divides] THEN
    AP_TERM_TAC THEN REWRITE_TAC[num_divides] THEN MATCH_MP_TAC(INTEGER_RULE
     `(x:int == y) (mod n) ==> (n divides x <=> n divides y)`) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_DIV; GSYM INT_OF_NUM_POW] THEN
    MATCH_MP_TAC INT_CONG_DIV2 THEN SIMP_TAC[INT_POW_LE; INT_POS] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!m. (x:int == y) (mod m) /\ n divides m ==> (y == x) (mod n)`) THEN
    EXISTS_TAC `(&2:int) pow dimindex(:N)` THEN REWRITE_TAC[IVAL_VAL_CONG] THEN
    ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 INT_POW)] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LT_EXISTS]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[INT_POW_ADD; INT_POW] THEN
    CONV_TAC INTEGER_RULE;
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
    MATCH_MP_TAC(MESON[ODD] `n = 0 ==> ~ODD n`) THEN
    SIMP_TAC[DIV_EQ_0; ARITH_EQ; EXP_EQ_0] THEN
    TRANS_TAC LTE_TRANS `2 EXP dimindex(:N)` THEN
    ASM_REWRITE_TAC[VAL_BOUND; LE_EXP; DIMINDEX_NONZERO; COND_ID]]);;

let BIT_IWORD = prove
 (`!i x. bit i (iword x:N word) <=>
         i < dimindex(:N) /\ ~(&2 divides (x div (&2 pow i)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIT_IVAL] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC(INTEGER_RULE
   `(x:int == y) (mod n) ==> (n divides x <=> n divides y)`) THEN
  MATCH_MP_TAC INT_CONG_DIV2 THEN SIMP_TAC[INT_POW_LE; INT_POS] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!m. (x:int == y) (mod m) /\ n divides m ==> (x == y) (mod n)`) THEN
  EXISTS_TAC `(&2:int) pow dimindex(:N)` THEN
  REWRITE_TAC[IVAL_IWORD_CONG] THEN
    ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 INT_POW)] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LT_EXISTS]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[INT_POW_ADD; INT_POW] THEN
    CONV_TAC INTEGER_RULE);;

let INT_REM_IVAL = prove
 (`!(w:N word) k.
        k <= dimindex(:N) ==> (ival w) rem (&2 pow k) = &(val w MOD 2 EXP k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_REM] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_POW; INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!n:int. (x == y) (mod n) /\ m divides n ==> (x == y) (mod m)`) THEN
  EXISTS_TAC `(&2:int) pow dimindex(:N)` THEN REWRITE_TAC[IVAL_VAL_CONG] THEN
  POP_ASSUM MP_TAC THEN
  SIMP_TAC[LE_EXISTS; INT_POW_ADD; LEFT_IMP_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN CONV_TAC INTEGER_RULE);;

let VAL_IVAL_REM = prove
 (`!x:N word. &(val x) = ival x rem &2 pow dimindex(:N)`,
  GEN_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[INT_REM_UNIQUE] THEN
  REWRITE_TAC[INT_ABS_POW; INT_ABS_NUM; INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[LE_0; VAL_BOUND] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; IVAL_VAL_CONG]);;

let INT_REM_IVAL_IWORD = prove
 (`!x k. k <= dimindex(:N)
         ==> ival(iword x:N word) rem &2 pow k = x rem &2 pow k`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS `x rem &2 pow dimindex(:N) rem &2 pow k` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM(REWRITE_RULE[GSYM INT_REM_EQ] IVAL_IWORD_CONG)];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INT_REM_REM_POW_MIN; ARITH_RULE `k <= n ==> MIN n k = k`]);;

let INT_DIVIDES_IVAL_IWORD = prove
 (`!n x. n <= dimindex(:N)
         ==> (&2 pow n divides ival(iword x:N word) <=> &2 pow n divides x)`,
  SIMP_TAC[INT_REM_IVAL_IWORD; GSYM INT_REM_EQ_0]);;

let FORALL_IVAL_GEN = prove
 (`!P. (!x:N word. P (ival x) x) <=>
       (!n. --(&2 pow (dimindex (:N) - 1)) <= n /\
            n < &2 pow (dimindex (:N) - 1)
            ==> P n (iword n))`,
  MESON_TAC[IVAL_IWORD; IWORD_IVAL; IVAL_BOUND]);;

let FORALL_IVAL = prove
 (`!P. (!x:N word. P(ival x)) <=>
       (!n. --(&2 pow (dimindex (:N) - 1)) <= n /\
            n < &2 pow (dimindex (:N) - 1)
            ==> P n)`,
  REWRITE_TAC[FORALL_IVAL_GEN]);;

let FORALL_IWORD = prove
 (`!P. (!x:N word. P x) <=> (!n. P(iword n))`,
  MESON_TAC[IWORD_IVAL]);;

let EXISTS_IWORD = prove
 (`!P. (?x:N word. P x) <=> (?n. P(iword n))`,
  MESON_TAC[IWORD_IVAL]);;

let IVAL_REM_2 = prove
 (`!x:N word. ival(x) rem &2 = &(bitval(bit 0 x))`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_MOD_2; GSYM INT_OF_NUM_REM] THEN
  REWRITE_TAC[INT_REM_EQ] THEN MATCH_MP_TAC(INTEGER_RULE
   `!m:int. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)`) THEN
  EXISTS_TAC `(&2:int) pow dimindex(:N)` THEN REWRITE_TAC[IVAL_VAL_CONG] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_divides] THEN
  REWRITE_TAC[divides; GSYM EVEN_EXISTS] THEN
  REWRITE_TAC[EVEN_EXP; ARITH; DIMINDEX_NONZERO]);;

let BIT_LSB_IWORD = prove
 (`!x. bit 0 (iword x:N word) = x rem &2 = &1`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM BITVAL_EQ_1] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM IVAL_REM_2] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!m:int. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)`) THEN
  EXISTS_TAC `(&2:int) pow dimindex(:N)` THEN REWRITE_TAC[IVAL_IWORD_CONG] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_divides] THEN
  REWRITE_TAC[divides; GSYM EVEN_EXISTS] THEN
  REWRITE_TAC[EVEN_EXP; ARITH; DIMINDEX_NONZERO]);;

let TWOS_COMPLEMENT_GEN = prove
 (`!p k n x:int.
        (&n == x) (mod (&2 pow (p + k))) /\
        n < 2 EXP (p + k) /\ --(&2 pow p) <= x /\ x < &2 pow p
        ==> n DIV 2 EXP p = (2 EXP k - 1) * bitval(x < &0) /\
            &n - &2 pow (p + k) * &(bitval(x < &0)) = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[bitval] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[INT_MUL_RZERO; INT_MUL_RID; INT_EQ_SUB_RADD;
                  GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_DIV] THEN
  SIMP_TAC[GSYM INT_OF_NUM_SUB; LE_1; EXP_EQ_0; ARITH_EQ;
           GSYM INT_OF_NUM_POW; INT_ADD_RID] THEN
  MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow (p + k)` THEN
     ASM_REWRITE_TAC[INTEGER_RULE
      `(n:int == x + p) (mod p) <=> (n == x) (mod p)`] THEN
     MATCH_MP_TAC(INT_ARITH
      `&0 <= x /\ x < p /\ &0 <= y /\ y < p
        ==> abs(x - y:int) < p`) THEN
     ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES; LE_0] THEN
     MP_TAC(SPECL [`p:num`; `p + k:num`; `&2:int`] INT_POW_MONO) THEN
     CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[LE_ADD] THEN
     REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
     INT_ARITH_TAC;
     DISCH_THEN SUBST1_TAC])
  THENL [ALL_TAC; REWRITE_TAC[INT_DIV_EQ_0] THEN ASM_INT_ARITH_TAC] THEN
  SIMP_TAC[INT_POW_ADD; INT_DIV_MUL_ADD; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ;
           INT_ARITH `x + k:int = k - &1 <=> x + &1 = &0`] THEN
  TRANS_TAC EQ_TRANS `(x + &1 * &2 pow p) div &2 pow p` THEN CONJ_TAC THENL
   [SIMP_TAC[INT_POW_ADD; INT_DIV_MUL_ADD; INT_POW_EQ_0; INT_OF_NUM_EQ;
             ARITH_EQ];
    REWRITE_TAC[INT_DIV_EQ_0] THEN ASM_INT_ARITH_TAC]);;

let TWOS_COMPLEMENT = prove
 (`!p n x:int.
        (&n == x) (mod (&2 pow p)) /\
        ~(p = 0) /\ n < 2 EXP p /\
        --(&2 pow (p - 1)) <= x /\ x < &2 pow (p - 1)
        ==> (2 EXP (p - 1) <= n <=> x < &0) /\
            n DIV (2 EXP (p - 1)) = bitval(x < &0) /\
            &n - &2 pow p * &(bitval(x < &0)) = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p - 1`; `1`; `n:num`; `x:int`] TWOS_COMPLEMENT_GEN) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[LE_1; SUB_ADD; MULT_CLAUSES] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\x. x = 0` o CONJUNCT1) THEN
  SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ; BITVAL_EQ_0] THEN
  REWRITE_TAC[GSYM NOT_LT] THEN CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* Bit operations on `num`.                                                  *)
(* ------------------------------------------------------------------------- *)

let numbit = new_definition `numbit i n = ODD(n DIV (2 EXP i))`;;

let NUMBIT_VAL = prove (`numbit i (val (e:N word)) = bit i e`,
  REWRITE_TAC [numbit; BIT_VAL]);;

(* * BIT_PRED `i` returns (None, `|- i = _0`) or (Some(`j`), `|- i = SUC j`)
     if `i` is a raw numeral (a numeral without the initial `NUMERAL`).
   * NUMBIT_CONV `numbit n i` proves `numbit n i = T` or `numbit n i = F` if
     `n` and `i` are numerals or raw numerals. *)

let BIT_PRED, NUMBIT_CONV =
  let i,j,n,B0,B1 = `i:num`,`j:num`,`n:num`,`BIT0`,`BIT1` in
  let B00 = CONJUNCT2 ARITH_ZERO in
  let th_0 = (PURE_REWRITE_RULE [NUMERAL] o prove)
   (`numbit i 0 = F`, REWRITE_TAC [numbit; DIV_0; ODD]) in
  let th00,th01 = (CONJ_PAIR o PURE_REWRITE_RULE [NUMERAL] o prove)
   (`numbit 0 (BIT0 n) = F /\ numbit 0 (BIT1 n) = T`,
     REWRITE_TAC [numbit; EXP; DIV_1; ARITH_ODD]) in
  let thS0,thS1 = (CONJ_PAIR o UNDISCH o prove) (`i = SUC j ==>
    numbit i (BIT0 n) = numbit j n /\ numbit i (BIT1 n) = numbit j n`,
    DISCH_THEN SUBST1_TAC THEN CONV_TAC BITS_ELIM_CONV THEN
    REWRITE_TAC [numbit; EXP; GSYM DIV_DIV;
      ARITH_RULE `(2 * n + 1) DIV 2 = n /\ (2 * n) DIV 2 = n`]) in
  let thB1S = prove (`BIT1 i = SUC (BIT0 i)`, REWRITE_TAC [ARITH_SUC]) in
  let thB10 = MATCH_MP (DISCH_ALL thS0) thB1S
  and thB11 = MATCH_MP (DISCH_ALL thS1) thB1S in
  let thSB1 = (UNDISCH o prove) (`i = SUC j ==> BIT0 i = SUC (BIT1 j)`,
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [ARITH_SUC]) in
  let thB00 = PROVE_HYP thSB1 (INST [`BIT0 i`,i;`BIT1 j`,j] thS0)
  and thB01 = PROVE_HYP thSB1 (INST [`BIT0 i`,i;`BIT1 j`,j] thS1) in
  let th0B00,th0B01 =
    let th = AP_TERM `numbit` (TRANS (AP_TERM `BIT0` (ASSUME `i = _0`)) B00) in
    TRANS (AP_THM th `BIT0 n`) th00, TRANS (AP_THM th `BIT1 n`) th01 in
  let thN = prove
   (`numbit (NUMERAL i) (NUMERAL n) = numbit i n`, REWRITE_TAC [NUMERAL]) in
  let get_suc th = Some (rand (rhs (concl th))), th in
  let rec mk_pred = function
  | Comb(Const("BIT0",_),i') ->
    (match mk_pred i' with
    | Some j', th -> get_suc (PROVE_HYP th (INST [i',i; j',j] thSB1))
    | None, th -> None, TRANS (AP_TERM B0 th) B00)
  | Comb(Const("BIT1",_),i') -> get_suc (INST [i',i] thB1S)
  | Const("_0",_) as i' -> None, REFL i'
  | _ -> failwith "BIT_PRED" in
  let rec go = function
  | i',Const("_0",_) -> INST [i',i] th_0
  | Const("_0",_),Comb(Const("BIT0",_),n') -> INST [n',n] th00
  | Const("_0",_),Comb(Const("BIT1",_),n') -> INST [n',n] th01
  | Comb(Const("BIT0",_),i'),Comb(Const("BIT0",_),n') ->
    go_B0 th0B00 thB00 i' n'
  | Comb(Const("BIT0",_),i'),Comb(Const("BIT1",_),n') ->
    go_B0 th0B01 thB01 i' n'
  | Comb(Const("BIT1",_),i'),Comb(Const("BIT0",_),n') ->
    TRANS (INST [i',i; n',n] thB10) (go (mk_comb (B0,i'),n'))
  | Comb(Const("BIT1",_),i'),Comb(Const("BIT1",_),n') ->
    TRANS (INST [i',i; n',n] thB11) (go (mk_comb (B0,i'),n'))
  | _ -> failwith "NUMBIT_CONV"
  and go_B0 th0 thS i' n' = match mk_pred i' with
  | Some j',th ->
    let th' = PROVE_HYP th (INST [i',i; j',j; n',n] thS) in
    TRANS th' (go (mk_comb (B1,j'), n'))
  | None, th -> PROVE_HYP th (INST [i',i; n',n] th0) in
  mk_pred, function
  | Comb(Comb(Const("numbit",_),
      Comb(Const("NUMERAL",_),i')),Comb(Const("NUMERAL",_),n')) ->
    TRANS (INST [i',i;n',n] thN) (go (i',n'))
  | Comb(Comb(Const("numbit",_),i'),n') -> go (i',n')
  | _ -> failwith "NUMBIT_CONV";;

let bits_of_num = new_definition
 `bits_of_num n = {i | numbit i n}`;;

let IN_BITS_OF_NUM = prove
 (`!n i. i IN bits_of_num n <=> ODD(n DIV 2 EXP i)`,
  REWRITE_TAC[bits_of_num; numbit; IN_ELIM_THM]);;

let BITS_OF_NUM_SUBSET_NUMSEG_LT = prove
 (`!n. bits_of_num n SUBSET {i | i < n}`,
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_BITS_OF_NUM] THEN
  MESON_TAC[DIV_LT; EVEN; LT_POW2_REFL; LET_TRANS; NOT_LE; NOT_EVEN]);;

let FINITE_BITS_OF_NUM = prove
 (`!n. FINITE(bits_of_num n)`,
  MESON_TAC[BITS_OF_NUM_SUBSET_NUMSEG_LT; FINITE_NUMSEG_LT; FINITE_SUBSET]);;

let NSUM_BITS_OF_NUM = prove
 (`!n. nsum (bits_of_num n) (\i. 2 EXP i) = n`,
  GEN_TAC THEN MP_TAC(SPECL [`2`; `n:num`; `n:num`] DIGITSUM_WORKS_GEN) THEN
  REWRITE_TAC[MOD_2_CASES; COND_RAND; MULT_CLAUSES] THEN
  REWRITE_TAC[GSYM NOT_ODD; COND_SWAP; GSYM NSUM_RESTRICT_SET] THEN
  SIMP_TAC[MOD_LT; LT_POW2_REFL] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(SPEC `n:num` BITS_OF_NUM_SUBSET_NUMSEG_LT) THEN
  REWRITE_TAC[bits_of_num; numbit] THEN SET_TAC[]);;

let BITS_OF_NUM_NSUM = prove
 (`!s. FINITE s ==> bits_of_num (nsum s (\i. 2 EXP i)) = s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_BITS_OF_NUM; ODD_MOD] THEN
  X_GEN_TAC `k:num` THEN MP_TAC(SPECL
    [`2`; `\i:num. 1`; `s:num->bool`; `k:num`] DIGITSUM_DIV_MOD) THEN
  ASM_SIMP_TAC[ARITH_RULE `1 < 2`; MULT_CLAUSES] THEN ARITH_TAC);;

let BITS_OF_NUM_EQ = prove
 (`!m n. bits_of_num m = bits_of_num n <=> m = n`,
  MESON_TAC[NSUM_BITS_OF_NUM]);;

let BITS_OF_NUM_GALOIS = prove
 (`!n s. bits_of_num n = s <=> FINITE s /\ nsum s (\i. 2 EXP i) = n`,
  MESON_TAC[FINITE_BITS_OF_NUM; BITS_OF_NUM_NSUM; NSUM_BITS_OF_NUM]);;

let NSUM_BITS_DIV = prove
 (`!s k. FINITE s
         ==> nsum s (\i. 2 EXP i) DIV 2 EXP k =
             nsum {i | i IN s /\ k <= i} (\i. 2 EXP (i - k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2`; `\i:num. 1`; `s:num->bool`; `k:num`] DIGITSUM_DIV) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 < 2`; MULT_CLAUSES]);;

let NSUM_BITS_MOD = prove
 (`!s k. FINITE s
         ==> nsum s (\i. 2 EXP i) MOD 2 EXP k =
             nsum {i | i IN s /\ i < k} (\i. 2 EXP i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2`; `\i:num. 1`; `s:num->bool`; `k:num`] DIGITSUM_MOD) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 < 2`; MULT_CLAUSES]);;

let NSUM_BITS_EQ = prove
 (`!s t. FINITE s /\ FINITE t
         ==> (nsum s (\i. 2 EXP i) = nsum t (\i. 2 EXP i) <=> s = t)`,
  MESON_TAC[BITS_OF_NUM_NSUM]);;

let BITSUM_BOUND = prove
 (`!s k. FINITE s
         ==> (nsum s (\i. 2 EXP i) < 2 EXP k <=> s SUBSET {i | i < k})`,
  SIMP_TAC[CONV_RULE(RAND_CONV SYM_CONV) (SPEC_ALL DIV_EQ_0); FINITE_RESTRICT;
           EXP_EQ_0; ARITH_EQ; NSUM_BITS_DIV; NSUM_EQ_0_IFF] THEN
  REWRITE_TAC[GSYM NOT_LE] THEN SET_TAC[]);;

let BITS_OF_NUM_SUBSET_NUMSEG_EQ = prove
 (`!n k. bits_of_num n SUBSET {i | i < k} <=> n < 2 EXP k`,
  SIMP_TAC[GSYM BITSUM_BOUND; FINITE_BITS_OF_NUM; NSUM_BITS_OF_NUM]);;

let BITSUM_DIVIDES = prove
 (`!s k. FINITE s
         ==> (2 EXP k divides nsum s (\i. 2 EXP i) <=>
              DISJOINT {i | i < k} s)`,
  SIMP_TAC[DIVIDES_DIV_MULT; NSUM_BITS_DIV; GSYM NSUM_RMUL; GSYM EXP_ADD] THEN
  SIMP_TAC[SUB_ADD; NSUM_BITS_EQ; FINITE_RESTRICT; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[GSYM NOT_LE] THEN SET_TAC[]);;

let BITS_OF_NUM_DISJOINT_NUMSEG_EQ = prove
 (`!n k. DISJOINT {i | i < k} (bits_of_num n) <=> 2 EXP k divides n`,
  SIMP_TAC[GSYM BITSUM_DIVIDES; FINITE_BITS_OF_NUM; NSUM_BITS_OF_NUM]);;

let BITS_OF_NUM_0 = prove
 (`bits_of_num 0 = {}`,
  REWRITE_TAC[IN_BITS_OF_NUM; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  REWRITE_TAC[DIV_0; ODD]);;

let BITS_OF_NUM_POW2 = prove
 (`!k. bits_of_num(2 EXP k) = {k}`,
  REWRITE_TAC[IN_BITS_OF_NUM; EXTENSION; IN_ELIM_THM; IN_SING] THEN
  REPEAT GEN_TAC THEN SIMP_TAC[DIV_EXP; ARITH_EQ] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ODD_EXP; ARITH] THEN ASM_ARITH_TAC);;

let BITS_OF_NUM_1 = prove
 (`bits_of_num 1 = {0}`,
  REWRITE_TAC[GSYM BITS_OF_NUM_POW2; EXP]);;

let BITS_OF_NUM_DIV = prove
 (`!n k. bits_of_num (n DIV 2 EXP k) = {i | (k + i) IN bits_of_num n}`,
  REWRITE_TAC[bits_of_num; numbit; IN_ELIM_THM; DIV_DIV; EXP_ADD]);;

let BITS_OF_NUM_MOD = prove
 (`!n k. bits_of_num (n MOD 2 EXP k) = {i | i IN bits_of_num n /\ i < k}`,
  SIMP_TAC[BITS_OF_NUM_GALOIS; FINITE_RESTRICT; FINITE_BITS_OF_NUM;
           GSYM NSUM_BITS_MOD; NSUM_BITS_OF_NUM]);;

let BITS_OF_NUM_MUL_ALT = prove
 (`(!n k. bits_of_num(2 EXP k * n) = {i | k <= i /\ i - k IN bits_of_num n}) /\
   (!n k. bits_of_num(n * 2 EXP k) = {i | k <= i /\ i - k IN bits_of_num n})`,
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
  REWRITE_TAC[] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC(SET_RULE
   `DISJOINT {i | ~P i} s /\ (!i. P i ==> (i IN s <=> Q i))
    ==> s = {i | P i /\ Q i}`) THEN
  REWRITE_TAC[NOT_LE; BITS_OF_NUM_DISJOINT_NUMSEG_EQ] THEN
  SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM; IN_BITS_OF_NUM; EXP_ADD] THEN
  SIMP_TAC[ADD_SUB2; DIV_MULT2; EXP_EQ_0; ARITH_EQ] THEN
  CONV_TAC NUMBER_RULE);;

let BITS_OF_NUM_MUL = prove
 (`(!n k. bits_of_num(2 EXP k * n) = IMAGE (\i. k + i) (bits_of_num n)) /\
   (!n k. bits_of_num(n * 2 EXP k) = IMAGE (\i. k + i) (bits_of_num n))`,
  REWRITE_TAC[BITS_OF_NUM_MUL_ALT] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  MESON_TAC[LE_EXISTS; ADD_SUB2]);;

let BITS_OF_NUM_ADD = prove
 (`!m n. DISJOINT (bits_of_num m) (bits_of_num n)
         ==> bits_of_num(m + n) = (bits_of_num m) UNION (bits_of_num n)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[BITS_OF_NUM_GALOIS; FINITE_UNION; FINITE_BITS_OF_NUM] THEN
  ASM_SIMP_TAC[NSUM_UNION; FINITE_BITS_OF_NUM; NSUM_BITS_OF_NUM]);;

let DISJOINT_BITS_HILO = prove
 (`!k h l. l < 2 EXP k
           ==> DISJOINT (bits_of_num(2 EXP k * h)) (bits_of_num l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ] THEN
  MATCH_MP_TAC(SET_RULE `DISJOINT t u ==> s SUBSET t ==> DISJOINT u s`) THEN
  REWRITE_TAC[BITS_OF_NUM_DISJOINT_NUMSEG_EQ] THEN
  CONV_TAC NUMBER_RULE);;

let DISJOINT_BITS_CLAUSES = prove
 (`(!k h l. l < 2 EXP k
            ==> DISJOINT (bits_of_num(2 EXP k * h)) (bits_of_num l)) /\
   (!k h l. l < 2 EXP k
            ==> DISJOINT (bits_of_num(h * 2 EXP k)) (bits_of_num l)) /\
   (!k h l. l < 2 EXP k
            ==> DISJOINT (bits_of_num l) (bits_of_num(2 EXP k * h))) /\
   (!k h l. l < 2 EXP k
            ==> DISJOINT (bits_of_num l) (bits_of_num(h * 2 EXP k))) /\
   (!m n k. DISJOINT (bits_of_num m) (bits_of_num n)
            ==> DISJOINT (bits_of_num(2 EXP k * m))
                         (bits_of_num(2 EXP k * n))) /\
   (!m n k. DISJOINT (bits_of_num m) (bits_of_num n)
            ==> DISJOINT (bits_of_num(m * 2 EXP k))
                         (bits_of_num(n * 2 EXP k))) /\
   (!m n k. DISJOINT (bits_of_num m) (bits_of_num n)
            ==> DISJOINT (bits_of_num(m DIV 2 EXP k))
                         (bits_of_num(n DIV 2 EXP k))) /\
   (!m n k. DISJOINT (bits_of_num m) (bits_of_num n)
            ==> DISJOINT (bits_of_num(m MOD 2 EXP k))
                         (bits_of_num(n MOD 2 EXP k)))`,
  REPLICATE_TAC 3 (GEN_REWRITE_TAC I [CONJ_ASSOC]) THEN CONJ_TAC THENL
   [MESON_TAC[DISJOINT_BITS_HILO; MULT_SYM; DISJOINT_SYM];
    SIMP_TAC[BITS_OF_NUM_DIV; BITS_OF_NUM_MOD; BITS_OF_NUM_MUL_ALT] THEN
    SET_TAC[]]);;

let DIV_MOD_DISJOINT_BITS = prove
 (`(!m n. DISJOINT (bits_of_num m) (bits_of_num n)
          ==> (m + n) DIV 2 EXP k = m DIV 2 EXP k + n DIV 2 EXP k) /\
   (!m n. DISJOINT (bits_of_num m) (bits_of_num n)
          ==> (m + n) MOD 2 EXP k = m MOD 2 EXP k + n MOD 2 EXP k)`,
  SIMP_TAC[GSYM BITS_OF_NUM_EQ; BITS_OF_NUM_ADD; DISJOINT_BITS_CLAUSES;
           BITS_OF_NUM_DIV; BITS_OF_NUM_MOD] THEN
  SET_TAC[]);;

let BITS_OF_WORD_WORD = prove
 (`!n. bits_of_word(word n:N word) =
       {i | i < dimindex(:N)} INTER bits_of_num n`,
  REWRITE_TAC[bits_of_num; bits_of_word; BIT_WORD; numbit] THEN SET_TAC[]);;

let BITS_OF_NUM_VAL = prove
 (`!x:N word. bits_of_num(val x) = bits_of_word(x)`,
  REWRITE_TAC[bits_of_num; bits_of_word; NUMBIT_VAL]);;

(* ------------------------------------------------------------------------- *)
(* A primitive operation for splitting numerals along powers of 2.           *)
(* ------------------------------------------------------------------------- *)

let num_shift_add = new_definition
  `num_shift_add a b n = a MOD 2 EXP n + b * 2 EXP n`;;

let num_shift_add_0 = prove
 (`num_shift_add a b 0 = b`,
  REWRITE_TAC [num_shift_add; EXP; MOD_1; MULT_CLAUSES; ADD]);;

let EXP_2_MOD_LT =
  GEN_ALL (REWRITE_RULE [GSYM (SPEC `a:num` MOD_LT_EQ)] EXP_2_NE_0);;

let num_shift_add_SUC = prove
 (`num_shift_add (BIT0 a) b (SUC n) = BIT0 (num_shift_add a b n) /\
   num_shift_add (BIT1 a) b (SUC n) = BIT1 (num_shift_add a b n)`,
  REWRITE_TAC [num_shift_add; EXP] THEN CONV_TAC BITS_ELIM_CONV THEN
  REWRITE_TAC [LEFT_ADD_DISTRIB; MOD_MULT2; MULT_AC] THEN
  REWRITE_TAC [ADD_AC; EQ_ADD_LCANCEL] THEN
  ONCE_REWRITE_TAC [SYM (MATCH_MP MOD_LT
    (MATCH_MP (ARITH_RULE `a < b ==> a * 2 + 1 < b * 2`)
      (SPECL [`a:num`;`n:num`] EXP_2_MOD_LT)))] THEN
  ONCE_REWRITE_TAC [GSYM MOD_ADD_MOD] THEN
  REWRITE_TAC [ONCE_REWRITE_RULE [MULT_SYM] MOD_MULT2; MOD_MOD_REFL]);;

let num_shift_add_lt = prove
 (`!a b n i. b < 2 EXP i ==> num_shift_add a b n < 2 EXP (i + n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [num_shift_add; EXP_ADD] THEN
  DISCH_TAC THEN MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `SUC b * 2 EXP n` THEN
  ASM_REWRITE_TAC [LE_MULT_RCANCEL; MULT_CLAUSES; ADD_SYM; LT_ADD_LCANCEL;
    EXP_2_MOD_LT; LE_SUC_LT]);;

let num_shift_add_mod = prove
 (`num_shift_add a (b MOD 2 EXP i) n = num_shift_add a b n MOD 2 EXP (i + n)`,
  ONCE_REWRITE_TAC [(SYM o MATCH_MP MOD_LT o SPEC_ALL)
    (MATCH_MP num_shift_add_lt (SPECL [`b:num`; `i:num`] EXP_2_MOD_LT))] THEN
  REWRITE_TAC [num_shift_add; EXP_ADD] THEN
  ONCE_REWRITE_TAC [GSYM MOD_ADD_MOD] THEN
  REWRITE_TAC [GSYM (ONCE_REWRITE_RULE [MULT_SYM] MOD_MULT2); MOD_MOD_REFL]);;

(* (NUM_SHIFT_ADD_CONV `num_shift_add a b i`), and
   (NUM_SHIFT_ADD_CORE `a` `b` `i`), will prove `|- num_shift_add a b i = n`
   where a,b,i,n are numerals or raw numerals. *)

let NUM_SHIFT_ADD_CORE, NUM_SHIFT_ADD_CONV =
  let i,j,a,b,e = `i:num`,`j:num`,`a:num`,`b:num`,`e:num` in
  let i0 = (UNDISCH o prove) (`i = _0 ==> num_shift_add a b i = b`,
    DISCH_THEN SUBST1_TAC THEN CONV_TAC BITS_ELIM_CONV THEN
    ACCEPT_TAC num_shift_add_0) in
  let B0S,B1S = (CONJ_PAIR o UNDISCH_ALL o prove)
   (`num_shift_add a b j = e ==> i = SUC j ==>
    num_shift_add (BIT0 a) b i = BIT0 e /\
    num_shift_add (BIT1 a) b i = BIT1 e`,
    DISCH_THEN (SUBST1_TAC o SYM) THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [num_shift_add_SUC]) in
  let ZS = REWRITE_RULE [ARITH_ZERO] (INST [`_0`,a] B0S)
  and B00 = REWRITE_RULE [ARITH_ZERO] (INST [`_0`,e] B0S) in
  let Z0 = REWRITE_RULE [ARITH_ZERO] (INST [`_0`,e] ZS) in
  let rec go a' b' i' = match BIT_PRED i' with
  | None, th -> PROVE_HYP th (INST [i',i; a',a; b',b] i0)
  | Some j', th ->
    PROVE_HYP th (match a' with
    | Comb(Const("BIT0",_),a') ->
      let th' = go a' b' j' in
      PROVE_HYP th' (match rhs (concl th') with
      | Const("_0",_) -> INST [i',i; j',j; a',a; b',b] B00
      | e' -> INST [e',e; i',i; j',j; a',a; b',b] B0S)
    | Comb(Const("BIT1",_),a') ->
      let th' = go a' b' j' in
      let e' = rhs (concl th') in
      PROVE_HYP th' (INST [e',e; i',i; j',j; a',a; b',b] B1S)
    | Const("_0",_) ->
      let th' = go a' b' j' in
      PROVE_HYP th' (match rhs (concl th') with
      | Const("_0",_) -> INST [i',i; j',j; a',a; b',b] Z0
      | e' -> INST [e',e; i',i; j',j; a',a; b',b] ZS)
    | _ -> failwith "NUM_SHIFT_ADD_CORE") in
  let pthn = (UNDISCH o prove)
   (`num_shift_add a b i = e ==>
     num_shift_add (NUMERAL a) (NUMERAL b) (NUMERAL i) = NUMERAL e`,
    REWRITE_TAC [NUMERAL]) in
  go, function
  | Comb(Comb(Comb(Const("num_shift_add",_), Comb(Const("NUMERAL",_),a')),
      Comb(Const("NUMERAL",_),b')), Comb(Const("NUMERAL",_),i')) ->
    let th = go a' b' i' in
    PROVE_HYP th (INST [a',a; b',b; i',i; rhs (concl th),e] pthn)
  | Comb(Comb(Comb(Const("num_shift_add",_),a'),b'),i') ->
    go a' b' i'
  | _ -> failwith "NUM_SHIFT_ADD_CONV";;

(* ------------------------------------------------------------------------- *)
(* Some "limiting" values with names in the style of C's "limits.h" macros.  *)
(* ------------------------------------------------------------------------- *)

let word_UINT_MAX = new_definition
 `word_UINT_MAX:N word = word(2 EXP dimindex(:N) - 1)`;;

let word_INT_MIN = new_definition
 `word_INT_MIN:N word = iword(--(&2 pow (dimindex(:N) - 1)))`;;

let word_INT_MAX = new_definition
 `word_INT_MAX:N word = iword(&2 pow (dimindex(:N) - 1) - &1)`;;

let WORD_INT_MIN = prove
 (`word_INT_MIN:N word = word(2 EXP (dimindex(:N) - 1))`,
  REWRITE_TAC[word_INT_MIN; WORD_IWORD; IWORD_EQ; GSYM INT_OF_NUM_POW] THEN
  MATCH_MP_TAC(INTEGER_RULE `&2 * x:int = y ==> (--x == x) (mod y)`) THEN
  REWRITE_TAC[GSYM(CONJUNCT2 INT_POW)] THEN
  SIMP_TAC[DIMINDEX_NONZERO; ARITH_RULE `~(n = 0) ==> SUC(n - 1) = n`]);;

let WORD_INT_MAX = prove
 (`word_INT_MAX:N word = word(2 EXP (dimindex(:N) - 1) - 1)`,
  REWRITE_TAC[word_INT_MAX; WORD_IWORD] THEN AP_TERM_TAC THEN
  SIMP_TAC[INT_OF_NUM_SUB; INT_OF_NUM_POW; LE_1; EXP_EQ_0; ARITH_EQ]);;

let VAL_WORD_UINT_MAX = prove
 (`val(word_UINT_MAX:N word) = 2 EXP dimindex(:N) - 1`,
  REWRITE_TAC[word_UINT_MAX; VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`; EXP_EQ_0] THEN ARITH_TAC);;

let IVAL_WORD_INT_MIN = prove
 (`ival(word_INT_MIN:N word) = --(&2 pow (dimindex(:N) - 1))`,
  REWRITE_TAC[word_INT_MIN] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[INT_LE_REFL; INT_ARITH `--a:int < a <=> &0 < a`] THEN
  SIMP_TAC[INT_LT_POW2]);;

let IVAL_WORD_INT_MAX = prove
 (`ival(word_INT_MAX:N word) = &2 pow (dimindex(:N) - 1) - &1`,
  REWRITE_TAC[word_INT_MAX] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[INT_ARITH `x - &1:int < x`] THEN
  MATCH_MP_TAC(INT_ARITH `&0:int < x ==> --x <= x - &1`) THEN
  SIMP_TAC[INT_LT_POW2]);;

let VAL_BOUND_ALT = prove
 (`!w:N word. val w <= val(word_UINT_MAX:N word)`,
  GEN_TAC THEN MP_TAC(ISPEC `w:N word` VAL_BOUND) THEN
  REWRITE_TAC[VAL_WORD_UINT_MAX] THEN ARITH_TAC);;

let IVAL_BOUND_ALT = prove
 (`!w:N word. ival(word_INT_MIN:N word) <= ival w /\
              ival w <= ival(word_INT_MAX:N word)`,
  GEN_TAC THEN MP_TAC(ISPEC `w:N word` IVAL_BOUND) THEN
  REWRITE_TAC[IVAL_WORD_INT_MAX; IVAL_WORD_INT_MIN] THEN INT_ARITH_TAC);;

let VAL_WORD_INT_MIN = prove
 (`val(word_INT_MIN:N word) = 2 EXP (dimindex(:N) - 1)`,
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; VAL_IVAL; GSYM INT_OF_NUM_POW] THEN
  REWRITE_TAC[MSB_IVAL; IVAL_WORD_INT_MIN] THEN
  SIMP_TAC[INT_NEG_LT0; INT_LT_POW2; BITVAL_CLAUSES; INT_MUL_RID] THEN
  REWRITE_TAC[INT_ARITH `--x + y:int = x <=> &2 * x = y`] THEN
  SIMP_TAC[GSYM(CONJUNCT2 INT_POW)] THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `SUC(n - 1) = n <=> ~(n = 0)`; DIMINDEX_NONZERO]);;

let INT_VAL_WORD_INT_MIN = prove
 (`&(val(word_INT_MIN:N word)):int = &2 pow (dimindex(:N) - 1)`,
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_EQ; VAL_WORD_INT_MIN]);;

let WORD_INT_MIN_ALT = prove
 (`word_INT_MIN:N word = word_of_bits {dimindex (:N) - 1}`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_INT_MIN; VAL_WORD_OF_BITS_SING] THEN
  REWRITE_TAC[ARITH_RULE `n - 1 < n <=> 1 <= n`; DIMINDEX_GE_1]);;

let BIT_WORD_INT_MIN = prove
 (`!i. bit i (word_INT_MIN:N word) <=> i = dimindex(:N) - 1`,
  REWRITE_TAC[WORD_INT_MIN_ALT; BIT_WORD_OF_BITS_SING] THEN
  REWRITE_TAC[DIMINDEX_GE_1; ARITH_RULE `n - 1 < n <=> 1 <= n`]);;

(* ------------------------------------------------------------------------- *)
(* Saturating versions of the conversions from N and Z to words.             *)
(* ------------------------------------------------------------------------- *)

let word_saturate = new_definition
 `(word_saturate:num->N word) n =
        if n > val(word_UINT_MAX:N word) then word_UINT_MAX
        else word n`;;

let iword_saturate = new_definition
 `(iword_saturate:int->N word) x =
        if x < ival(word_INT_MIN:N word) then word_INT_MIN
        else if x > ival(word_INT_MAX:N word) then word_INT_MAX
        else iword x`;;

(* ------------------------------------------------------------------------- *)
(* Population count (= number of 1s in a word), as a mathematical number.    *)
(* ------------------------------------------------------------------------- *)

let word_popcount = new_definition
 `word_popcount (x:N word) = CARD(bits_of_word x)`;;

let HAS_SIZE_BITS_OF_WORD_POPCOUNT = prove
 (`!x:N word. (bits_of_word x) HAS_SIZE word_popcount x`,
  REWRITE_TAC[word_popcount; HAS_SIZE; FINITE_BITS_OF_WORD]);;

let WORD_POPCOUNT_BOUND = prove
 (`!x:N word. word_popcount x <= dimindex(:N)`,
  GEN_TAC THEN REWRITE_TAC[word_popcount; bits_of_word] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_LT] THEN
  MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[BIT_TRIVIAL; NOT_LT]);;

let WORD_POPCOUNT_BOUND_SIZE = prove
 (`!(x:N word) n. val x < 2 EXP n ==> word_popcount x <= n`,
  REWRITE_TAC[GSYM UPPER_BITS_ZERO] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_popcount] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_LT] THEN
  MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[bits_of_word; SUBSET; IN_ELIM_THM] THEN
  ASM_MESON_TAC[NOT_LT]);;

let WORD_POPCOUNT_EQ_0 = prove
 (`!x:N word. word_popcount x = 0 <=> x = word 0`,
  SIMP_TAC[CARD_EQ_0; word_popcount; FINITE_BITS_OF_WORD] THEN
  REWRITE_TAC[BITS_OF_WORD_EQ_EMPTY]);;

let WORD_POPCOUNT_0 = prove
 (`word_popcount(word 0) = 0`,
  REWRITE_TAC[WORD_POPCOUNT_EQ_0]);;

let WORD_POPCOUNT_1 = prove
 (`word_popcount(word 1) = 1`,
  REWRITE_TAC[word_popcount; BITS_OF_WORD_1; CARD_SING]);;

let WORD_POPCOUNT_BITVAL = prove
 (`!b. word_popcount(word(bitval b):N word) <= 1`,
  GEN_TAC THEN REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[WORD_POPCOUNT_0; WORD_POPCOUNT_1; LE_0; LE_REFL]);;

let WORD_POPCOUNT_NSUM = prove
 (`!x:N word.
        word_popcount x = nsum {i | i < dimindex(:N)} (\i. bitval(bit i x))`,
  GEN_TAC THEN REWRITE_TAC[bitval; GSYM NSUM_RESTRICT_SET] THEN
  SIMP_TAC[NSUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[word_popcount; GSYM BIT_GUARD; IN_ELIM_THM; MULT_CLAUSES] THEN
  REWRITE_TAC[bits_of_word]);;

let WORD_POPCOUNT_LE_BITS = prove
 (`!(x:M word) (y:N word).
     (!i. i < dimindex(:M) /\ bit i x ==> bit i y)
     ==> word_popcount x <= word_popcount y`,
  REWRITE_TAC[GSYM BITS_OF_WORD_SUBSET_ALT; word_popcount] THEN
  SIMP_TAC[CARD_SUBSET; FINITE_BITS_OF_WORD]);;

let WORD_POPCOUNT_WORD_OF_BITS_GEN = prove
 (`!s. word_popcount(word_of_bits s:N word) =
       CARD({i | i < dimindex(:N)} INTER s)`,
  REWRITE_TAC[word_popcount; BITS_OF_WORD_OF_BITS; INTER_COMM]);;

let WORD_POPCOUNT_WORD_OF_BITS = prove
 (`!s. s SUBSET {i | i < dimindex(:N)}
       ==> word_popcount(word_of_bits s:N word) = CARD s`,
  REWRITE_TAC[WORD_POPCOUNT_WORD_OF_BITS_GEN] THEN
  MESON_TAC[SUBSET_INTER_ABSORPTION; INTER_COMM]);;

(* ------------------------------------------------------------------------- *)
(* Parity (= evenness or oddity of the popcount).                            *)
(* ------------------------------------------------------------------------- *)

let word_evenparity = new_definition
 `word_evenparity (x:N word) <=> EVEN(word_popcount x)`;;

let word_oddparity = new_definition
 `word_oddparity (x:N word) <=> ODD(word_popcount x)`;;

let NOT_WORD_EVENPARITY = prove
 (`!x:N word. ~(word_evenparity x) <=> word_oddparity x`,
  REWRITE_TAC[word_evenparity; word_oddparity; NOT_EVEN]);;

let NOT_WORD_ODDPARITY = prove
 (`!x:N word. ~(word_oddparity x) <=> word_evenparity x`,
  REWRITE_TAC[word_evenparity; word_oddparity; NOT_ODD]);;

let WORD_EVENPARITY_0 = prove
 (`word_evenparity(word 0:N word)`,
  REWRITE_TAC[word_evenparity; WORD_POPCOUNT_0; EVEN]);;

let WORD_ODDPARITY_0 = prove
 (`~word_oddparity(word 0:N word)`,
  REWRITE_TAC[NOT_WORD_ODDPARITY; WORD_EVENPARITY_0]);;

let WORD_EVENPARITY_1 = prove
 (`~word_evenparity(word 1:N word)`,
  REWRITE_TAC[word_evenparity; WORD_POPCOUNT_1] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let WORD_ODDPARITY_1 = prove
 (`word_oddparity(word 1:N word)`,
  REWRITE_TAC[GSYM NOT_WORD_EVENPARITY; WORD_EVENPARITY_1]);;

(* ------------------------------------------------------------------------- *)
(* Modular arithmetic operations in general, unsigned and signed.            *)
(* ------------------------------------------------------------------------- *)

let modular = new_definition
 `modular op (x:(N)word) (y:(N)word) = word(op (val x) (val y)):(N)word`;;

let VAL_MODULAR = prove
 (`!op x y:(N)word.
        val(modular op x y) = (op (val x) (val y)) MOD (2 EXP dimindex(:N))`,
  REWRITE_TAC[modular; VAL_WORD]);;

let CONG_MODULAR = prove
 (`!op x y:(N)word.
       (val(modular op x y) == op (val x) (val y))
       (mod (2 EXP dimindex(:N)))`,
  REWRITE_TAC[VAL_MODULAR; CONG_LMOD] THEN CONV_TAC NUMBER_RULE);;

let imodular = new_definition
 `imodular op (x:(N)word) (y:(N)word) =
        iword(op (ival x) (ival y)):(N)word`;;

let CONG_IMODULAR = prove
 (`!op x y:(N)word.
       (ival(imodular op x y) == op (ival x) (ival y))
       (mod (&2 pow (dimindex(:N))))`,
  REWRITE_TAC[imodular; IVAL_IWORD_CONG]);;

(* ------------------------------------------------------------------------- *)
(* Relational operations in general w.r.t. unsigned or signed value.         *)
(* ------------------------------------------------------------------------- *)

let relational2 = new_definition
 `relational2 r (x:(N)word) (y:(N)word) :bool = r (val x) (val y)`;;

let irelational2 = new_definition
 `irelational2 r (x:(N)word) (y:(N)word) :bool = r (ival x) (ival y)`;;

(* ------------------------------------------------------------------------- *)
(* Bitwise operations in general.                                            *)
(* ------------------------------------------------------------------------- *)

let bitwise1 = new_definition
 `(bitwise1 op:N word->N word) x = mk_word(lambda i. op(bitvector x$i))`;;

let bitwise2 = new_definition
 `(bitwise2 op:N word->N word->N word) x y =
        mk_word(lambda i. op (bitvector x$i) (bitvector y$i))`;;

let BIT_BITWISE1 = prove
 (`!op (x:N word) k.
        bit k (bitwise1 op x) <=>
        k < dimindex(:N) /\ op(bit k x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bit] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[bitwise1; word_tybij] THEN
  MATCH_MP_TAC LAMBDA_BETA THEN ASM_ARITH_TAC);;

let BIT_BITWISE2 = prove
 (`!op (x:N word) (y:N word) k.
        bit k (bitwise2 op x y) <=>
        k < dimindex(:N) /\ op (bit k x) (bit k y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bit] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[bitwise2; word_tybij] THEN
  MATCH_MP_TAC LAMBDA_BETA THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The main word operations. Where there is any meaningful difference        *)
(* between unsigned and signed we use a "u" or an "i" in the names.          *)
(* ------------------------------------------------------------------------- *)

let word_not = new_definition
 `word_not = bitwise1 (~)`;;

let BIT_WORD_NOT = prove
 (`!(x:N word) k. bit k (word_not x) <=> k < dimindex(:N) /\ ~bit k x`,
  REWRITE_TAC[word_not; BIT_BITWISE1]);;

let BITS_OF_WORD_NOT = prove
 (`!w:N word. bits_of_word(word_not w) =
              {i | i < dimindex(:N)} DIFF bits_of_word w`,
  REWRITE_TAC[bits_of_word; BIT_WORD_NOT] THEN SET_TAC[]);;

let WORD_OF_BITS_DIFF = prove
 (`!s t. {i | i < dimindex(:N)} SUBSET s
         ==> word_of_bits(s DIFF t):N word = word_not(word_of_bits t)`,
  REWRITE_TAC[GSYM BITS_OF_WORD_EQ; BITS_OF_WORD_NOT] THEN
  REWRITE_TAC[BITS_OF_WORD_OF_BITS] THEN SET_TAC[]);;

let VAL_WORD_NOT = prove
 (`!w:N word. val(word_not w) = 2 EXP dimindex(:N) - 1 - val w`,
  GEN_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `(m + n) + 1 = p ==> m = p - 1 - n`) THEN
  SIMP_TAC[val_def; GSYM NSUM_ADD; FINITE_NUMSEG_LT] THEN
  SIMP_TAC[GSYM LEFT_ADD_DISTRIB; BIT_WORD_NOT] THEN
  SIMP_TAC[BITVAL_NOT; BITVAL_BOUND; SUB_ADD; MULT_CLAUSES] THEN
  SPEC_TAC(`dimindex(:N)`,`k:num`) THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; EXP; ADD_CLAUSES; MULT_CLAUSES] THEN
  ASM_ARITH_TAC);;

let INT_VAL_WORD_NOT = prove
 (`!x:N word. &(val(word_not x)):int = &2 pow dimindex(:N) - &1 - &(val x)`,
  GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_NOT; ARITH_RULE `n - 1 - m = n - (m + 1)`] THEN
  W(MP_TAC o PART_MATCH (rand o rand) INT_OF_NUM_SUB o lhand o snd) THEN
  REWRITE_TAC[VAL_BOUND; ARITH_RULE `x + 1 <= n <=> x < n`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_POW] THEN
  INT_ARITH_TAC);;

let REAL_VAL_WORD_NOT = prove
 (`!x:N word. &(val(word_not x)):real = &2 pow dimindex(:N) - &1 - &(val x)`,
  GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_NOT; ARITH_RULE `n - 1 - m = n - (m + 1)`] THEN
  W(MP_TAC o PART_MATCH (rand o rand) REAL_OF_NUM_SUB o lhand o snd) THEN
  REWRITE_TAC[VAL_BOUND; ARITH_RULE `x + 1 <= n <=> x < n`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_POW] THEN
  REAL_ARITH_TAC);;

let WORD_POPCOUNT_NOT = prove
 (`!x:N word. word_popcount(word_not x) = dimindex(:N) - word_popcount x`,
  GEN_TAC THEN MATCH_MP_TAC(ARITH_RULE
   `x + y:num = z ==> x = z - y`) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_LT] THEN
  REWRITE_TAC[word_popcount] THEN MATCH_MP_TAC CARD_UNION_EQ THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; BITS_OF_WORD_NOT] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `s DIFF t UNION t = s <=> t SUBSET s`] THEN
  REWRITE_TAC[bits_of_word; SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[BIT_TRIVIAL; NOT_LT]);;

let word_and = new_definition
 `word_and = bitwise2 (/\)`;;

let BIT_WORD_AND = prove
 (`!(x:N word) (y:N word) k.
        bit k (word_and x y) <=>
        k < dimindex(:N) /\ bit k x /\ bit k y`,
  REWRITE_TAC[word_and; BIT_BITWISE2]);;

let BIT_WORD_AND_ALT = prove
 (`!(x:N word) y k. bit k (word_and x y) <=> bit k x /\ bit k y`,
  MESON_TAC[BIT_WORD_AND; BIT_TRIVIAL; NOT_LT]);;

let BITS_OF_WORD_AND = prove
 (`!v w:N word.
        bits_of_word(word_and v w) = bits_of_word v INTER bits_of_word w`,
  REWRITE_TAC[bits_of_word; BIT_WORD_AND] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
  MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let WORD_AND_EQ_0 = prove
 (`!v w:N word.
        word_and v w = word 0 <=> DISJOINT (bits_of_word v) (bits_of_word w)`,
  REWRITE_TAC[GSYM BITS_OF_WORD_EQ; BITS_OF_WORD_AND; BITS_OF_WORD_0] THEN
  SET_TAC[]);;

let WORD_OF_BITS_INTER = prove
 (`!s t. word_of_bits(s INTER t):N word =
         word_and (word_of_bits s) (word_of_bits t)`,
  REWRITE_TAC[GSYM BITS_OF_WORD_EQ; BITS_OF_WORD_AND] THEN
  REWRITE_TAC[BITS_OF_WORD_OF_BITS] THEN SET_TAC[]);;

let WORD_AND_WORD_OF_BITS_SING = prove
 (`!(w:N word) k.
        word_and w (word_of_bits {k}) =
        if bit k w then word_of_bits {k} else word 0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[WORD_EQ_BITS; BIT_WORD_AND; BIT_WORD_OF_BITS; BIT_WORD_0] THEN
  ASM SET_TAC[]);;

let WORD_OF_BITS_SING_AND_WORD = prove
 (`!(w:N word) k.
        word_and (word_of_bits {k}) w =
        if bit k w then word_of_bits {k} else word 0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[WORD_EQ_BITS; BIT_WORD_AND; BIT_WORD_OF_BITS; BIT_WORD_0] THEN
  ASM SET_TAC[]);;

let WORD_AND_POW2 = prove
 (`(!(x:N word) k.
        word_and x (word(2 EXP k)) = word(2 EXP k * bitval(bit k x))) /\
   (!(x:N word) k.
        word_and (word(2 EXP k)) x = word(2 EXP k * bitval(bit k x)))`,
  REWRITE_TAC[AND_FORALL_THM; bitval] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_AND; BIT_WORD_POW2; BIT_WORD_0] THEN
  ASM_MESON_TAC[]);;

let VAL_WORD_AND_POW2 = prove
 (`(!(x:N word) k.
        val(word_and x (word(2 EXP k))) = 2 EXP k * bitval(bit k x)) /\
   (!(x:N word) k.
        val(word_and (word(2 EXP k)) x) = 2 EXP k * bitval(bit k x))`,
  REWRITE_TAC[WORD_AND_POW2] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[bitval] THEN
  COND_CASES_TAC THEN REWRITE_TAC[MULT_CLAUSES; LT_EXP; EXP_LT_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let WORD_AND_POW2_BITVAL = prove
 (`(!(x:N word) k b.
        word_and x (word(2 EXP k * bitval b)) =
        word(2 EXP k * bitval(bit k x /\ b))) /\
   (!(x:N word) k b.
        word_and (word(2 EXP k * bitval b)) x =
        word(2 EXP k * bitval(b /\ bit k x)))`,
  REPEAT STRIP_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES] THEN
  REWRITE_TAC[WORD_AND_POW2; WORD_AND_EQ_0; BITS_OF_WORD_0] THEN
  REWRITE_TAC[DISJOINT_EMPTY]);;

let VAL_WORD_AND_POW2_BITVAL = prove
 (`(!(x:N word) k b.
        val(word_and x (word(2 EXP k * bitval b))) =
        2 EXP k * bitval(bit k x /\ b)) /\
   (!(x:N word) k b.
        val(word_and (word(2 EXP k * bitval b)) x) =
        2 EXP k * bitval(b /\ bit k x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_AND_POW2_BITVAL] THEN
  MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[bitval] THEN
  COND_CASES_TAC THEN REWRITE_TAC[MULT_CLAUSES; LT_EXP; EXP_LT_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let VAL_WORD_AND_LE = prove
 (`(!x y:N word. val(word_and x y) <= val x) /\
   (!x y:N word. val(word_and x y) <= val y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[val_def] THEN MATCH_MP_TAC NSUM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN X_GEN_TAC `i:num` THEN
  SIMP_TAC[IN_ELIM_THM; BIT_WORD_AND; LE_MULT_LCANCEL; LE_BITVAL]);;

let VAL_WORD_AND_LE_MIN = prove
 (`!x y:N word. val(word_and x y) <= MIN (val x) (val y)`,
  REWRITE_TAC[ARITH_RULE `x <= MIN y z <=> x <= y /\ x <= z`] THEN
  REWRITE_TAC[VAL_WORD_AND_LE]);;

let VAL_WORD_AND_WORD_LE = prove
 (`(!(x:N word) n. val(word_and x (word n)) <= n) /\
   (!(x:N word) n. val(word_and (word n) x) <= n)`,
  MESON_TAC[VAL_WORD_AND_LE; LE_TRANS; LE_REFL; VAL_WORD_LE]);;

let WORD_POPCOUNT_AND = prove
 (`!x y:N word.
      word_popcount(word_and x y) <= MIN (word_popcount x) (word_popcount y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `x <= MIN a b <=> x <= a /\ x <= b`] THEN
  CONJ_TAC THEN MATCH_MP_TAC WORD_POPCOUNT_LE_BITS THEN
  SIMP_TAC[BIT_WORD_AND]);;

let word_or = new_definition
 `word_or = bitwise2 (\/)`;;

let BIT_WORD_OR = prove
 (`!(x:N word) (y:N word) k.
        bit k (word_or x y) <=>
        k < dimindex(:N) /\ (bit k x \/ bit k y)`,
  REWRITE_TAC[word_or; BIT_BITWISE2]);;

let BIT_WORD_OR_ALT = prove
 (`!(x:N word) y k. bit k (word_or x y) <=> bit k x \/ bit k y`,
  MESON_TAC[BIT_WORD_OR; BIT_TRIVIAL; NOT_LT]);;

let BITS_OF_WORD_OR = prove
 (`!v w:N word.
        bits_of_word(word_or v w) = bits_of_word v UNION bits_of_word w`,
  REWRITE_TAC[bits_of_word; BIT_WORD_OR] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
  MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let WORD_OF_BITS_UNION = prove
 (`!s t. word_of_bits(s UNION t):N word =
         word_or (word_of_bits s) (word_of_bits t)`,
  REWRITE_TAC[GSYM BITS_OF_WORD_EQ; BITS_OF_WORD_OR] THEN
  REWRITE_TAC[BITS_OF_WORD_OF_BITS] THEN SET_TAC[]);;

let VAL_WORD_OR_LE = prove
 (`(!x y:N word. val x <= val(word_or x y)) /\
   (!x y:N word. val y <= val(word_or x y))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_LE_BITS THEN
  SIMP_TAC[BIT_WORD_OR]);;

let VAL_WORD_OR_LE_MAX = prove
 (`(!x y:N word. MAX (val x) (val y) <= val(word_or x y))`,
  REWRITE_TAC[ARITH_RULE `MAX y z <= x <=> y <= x /\ z <= x`] THEN
  REWRITE_TAC[VAL_WORD_OR_LE]);;

let WORD_POPCOUNT_OR = prove
 (`!x y:N word.
      word_popcount(word_or x y) <= word_popcount x + word_popcount y`,
  REWRITE_TAC[word_popcount; BITS_OF_WORD_OR] THEN
  SIMP_TAC[CARD_UNION_LE; FINITE_BITS_OF_WORD]);;

let WORD_POPCOUNT_OR_DISJOINT = prove
 (`!x y:N word.
        word_and x y = word 0
        ==> word_popcount(word_or x y) = word_popcount x + word_popcount y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM BITS_OF_WORD_EQ_EMPTY] THEN
  SIMP_TAC[word_popcount; BITS_OF_WORD_OR; BITS_OF_WORD_AND;
           CARD_UNION; FINITE_BITS_OF_WORD]);;

let word_xor = new_definition
 `word_xor = bitwise2 (\x y. ~(x <=> y))`;;

let BIT_WORD_XOR = prove
 (`!(x:N word) (y:N word) k.
        bit k (word_xor x y) <=>
        k < dimindex(:N) /\ ~(bit k x <=> bit k y)`,
  REWRITE_TAC[word_xor; BIT_BITWISE2]);;

let BIT_WORD_XOR_ALT = prove
 (`!(x:N word) y k. bit k (word_xor x y) <=> ~(bit k x <=> bit k y)`,
  MESON_TAC[BIT_WORD_XOR; BIT_TRIVIAL; NOT_LT]);;

let VAL_WORD_ADD_AND_XOR,VAL_WORD_ADD_AND_OR = (CONJ_PAIR o prove)
 (`(!x y:N word. val x + val y = 2 * val(word_and x y) + val(word_xor x y)) /\
   (!x y:N word. val x + val y = val(word_and x y) + val(word_or x y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[val_def; GSYM NSUM_LMUL] THEN
  SIMP_TAC[GSYM NSUM_ADD; FINITE_NUMSEG_LT] THEN MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM; BIT_WORD_AND; BIT_WORD_XOR; BIT_WORD_OR] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY ASM_CASES_TAC [`bit i (x:N word)`; `bit i (y:N word)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN ARITH_TAC);;

let VAL_WORD_OR_DISJOINT = prove
 (`!x y:N word.
        word_and x y = word 0 ==> val(word_or x y) = val x + val y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[VAL_WORD_ADD_AND_OR] THEN
  ASM_REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES]);;

let VAL_WORD_OR_AND_XOR = prove
 (`!x y:N word. val(word_or x y) = val(word_and x y) + val(word_xor x y)`,
  ONCE_REWRITE_TAC[ARITH_RULE `a = b + c <=> b + a = 2 * b + c`] THEN
  MESON_TAC[VAL_WORD_ADD_AND_XOR; VAL_WORD_ADD_AND_OR]);;

let REAL_VAL_WORD_XOR = prove
 (`!x y:N word. &(val(word_xor x y)):real =
                (&(val x) + &(val y)) - &2 * &(val(word_and x y))`,
  REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_ADD_AND_XOR] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC);;

let word_add = new_definition
 `word_add = modular (+)`;;

let VAL_WORD_ADD = prove
 (`!x y:(N) word.
        val(word_add x y) = (val(x) + val(y)) MOD (2 EXP dimindex(:N))`,
  REWRITE_TAC[word_add; VAL_MODULAR]);;

let VAL_WORD_ADD_CASES = prove
 (`!x y:(N) word.
        val(word_add x y) =
        if val x + val y < 2 EXP dimindex(:N) then val x + val y
        else (val x + val y) - 2 EXP dimindex(:N)`,
  SIMP_TAC[VAL_WORD_ADD; VAL_BOUND; MOD_ADD_CASES]);;

let VAL_WORD_ADC_CASES = prove
 (`!c x y:(N) word.
        val(c) < 2
        ==> val(word_add (word_add x y) c) =
            if val x + val y + val c < 2 EXP dimindex(:N)
            then val x + val y + val c
            else (val x + val y + val c) - 2 EXP dimindex(:N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM ADD_ASSOC] THEN
  MATCH_MP_TAC MOD_CASES THEN MATCH_MP_TAC(ARITH_RULE
   `x < n /\ y < n /\ c < 2 ==> x + y + c < 2 * n`) THEN
  ASM_REWRITE_TAC[VAL_BOUND]);;

let INT_VAL_WORD_ADD_CASES = prove
 (`!x y:(N) word.
      &(val(word_add x y)):int =
      if &(val x) + &(val y):int < &2 pow dimindex(:N) then &(val x) + &(val y)
      else (&(val x) + &(val y)) - &2 pow dimindex(:N)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_ADD_CASES] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_POW; INT_OF_NUM_LT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[NOT_LT; INT_OF_NUM_SUB]);;

let CONG_WORD_ADD = prove
 (`!x y:(N)word.
        (val(word_add x y) == val x + val y) (mod (2 EXP dimindex(:N)))`,
  REWRITE_TAC[word_add; CONG_MODULAR]);;

let INT_CONG_WORD_ADD = prove
 (`!x y:N word.
    (&(val(word_add x y)):int == &(val x) + &(val y))
    (mod (&2 pow dimindex(:N)))`,
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent; CONG_WORD_ADD]);;

let WORD_ADD = prove
 (`!x y. word(x + y):N word = word_add (word x) (word y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_CONG] THEN
  MP_TAC(ISPECL [`word x:N word`; `word y:N word`] CONG_WORD_ADD) THEN
  MAP_EVERY (MP_TAC o C ISPEC VAL_WORD_CONG)
   [`x + y:num`; `y:num`; `x:num`] THEN
  CONV_TAC NUMBER_RULE);;

let ICONG_WORD_ADD = prove
 (`!x y:(N)word.
        (ival(word_add x y) == ival x + ival y) (mod (&2 pow dimindex(:N)))`,
  REPEAT GEN_TAC THEN MAP_EVERY (MP_TAC o C SPEC IVAL_VAL_CONG)
   [`x:N word`; `y:N word`; `word_add x y:N word`] THEN
  MP_TAC(ISPECL [`x:N word`; `y:N word`] CONG_WORD_ADD) THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_ADD] THEN
  CONV_TAC INTEGER_RULE);;

let IWORD_INT_ADD = prove
 (`!x y. iword(x + y):N word = word_add (iword x) (iword y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IVAL_CONG] THEN
  MP_TAC(ISPECL [`iword x:N word`; `iword y:N word`] ICONG_WORD_ADD) THEN
  MAP_EVERY (MP_TAC o C ISPEC IVAL_IWORD_CONG)
   [`x + y:int`; `y:int`; `x:int`] THEN
  CONV_TAC INTEGER_RULE);;

let WORD_ADD_IMODULAR = prove
 (`(word_add:N word->N word->N word) = imodular ( + )`,
  REWRITE_TAC[FUN_EQ_THM; GSYM IVAL_CONG] THEN
  ASM_MESON_TAC[ICONG_WORD_ADD; CONG_IMODULAR; INTEGER_RULE
   `(a:int == b) (mod n) /\ (c == b) (mod n) ==> (a == c) (mod n)`]);;

let ODD_VAL_WORD = prove
 (`!n. ODD(val(word n:N word)) <=> ODD n`,
   SIMP_TAC[VAL_WORD; ODD_MOD_EVEN; EVEN_EXP; ARITH; DIMINDEX_NONZERO]);;

let EVEN_VAL_WORD = prove
 (`!n. EVEN(val(word n:N word)) <=> EVEN n`,
  REWRITE_TAC[GSYM NOT_ODD; ODD_VAL_WORD]);;

let ODD_VAL_WORD_ADD = prove
 (`!x y:N word. ODD(val(word_add x y)) <=> ~(ODD(val x) <=> ODD(val y))`,
  SIMP_TAC[VAL_WORD_ADD; ODD_MOD_EVEN; EVEN_EXP; ARITH; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[ODD_ADD]);;

let EVEN_VAL_WORD_ADD = prove
 (`!x y:N word. EVEN(val(word_add x y)) <=> (EVEN(val x) <=> EVEN(val y))`,
  REWRITE_TAC[GSYM NOT_ODD; ODD_VAL_WORD_ADD] THEN CONV_TAC TAUT);;

let word_sub = new_definition
 `(word_sub:(N)word->(N)word->(N)word) =
        modular (\x y. x + (2 EXP dimindex(:N) - y))`;;

let VAL_WORD_SUB = prove
 (`!x y:(N) word.
        val(word_sub x y) =
        (val(x) + (2 EXP dimindex(:N) - val(y))) MOD (2 EXP dimindex(:N))`,
  REWRITE_TAC[word_sub; VAL_MODULAR]);;

let VAL_WORD_SUB_CASES = prove
 (`!x y:(N) word.
        val(word_sub x y) =
        if val y <= val x then val(x) - val(y)
        else val(x) + (2 EXP dimindex(:N) - val(y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUB] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[MOD_LT] THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1`;
    MATCH_MP_TAC MOD_LT] THEN
  MAP_EVERY (MP_TAC o C ISPEC VAL_BOUND) [`x:N word`; `y:N word`] THEN
  ASM_ARITH_TAC);;

let INT_VAL_WORD_SUB_CASES = prove
 (`!x y:(N) word.
        &(val(word_sub x y)):int =
        if &(val y):int <= &(val x) then &(val x) - &(val y)
        else &(val x) + (&2 pow dimindex(:N) - &(val y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_POW; INT_OF_NUM_LE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[INT_OF_NUM_ADD; INT_OF_NUM_SUB; VAL_BOUND; LT_IMP_LE]);;

let CONG_WORD_SUB = prove
 (`!x y:(N)word.
        (val(word_sub x y) + val y == val x) (mod (2 EXP dimindex(:N)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONG; VAL_MODULAR; word_sub] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  SIMP_TAC[VAL_BOUND; ARITH_RULE `y:num < n ==> (x + n - y) + y = x + n`] THEN
  REWRITE_TAC[GSYM CONG] THEN CONV_TAC NUMBER_RULE);;

let INT_CONG_WORD_SUB = prove
 (`!x y:N word.
    (&(val(word_sub x y)):int == &(val x) - &(val y))
    (mod (&2 pow dimindex(:N)))`,
  REWRITE_TAC[INTEGER_RULE
   `(z:int == x - y) (mod n) <=> (z + y == x) (mod n)`] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; CONG_WORD_SUB; GSYM num_congruent]);;

let INT_VAL_WORD_SUB = prove
 (`!x y:N word.
        &(val(word_sub x y:N word)):int =
        (&(val x) - &(val y)) rem &2 pow dimindex(:N)`,
   REWRITE_TAC[GSYM(REWRITE_RULE[GSYM INT_REM_EQ] INT_CONG_WORD_SUB)] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM; VAL_MOD_REFL]);;

let ICONG_WORD_SUB = prove
 (`!x y:N word.
        (ival(word_sub x y) == ival x - ival y) (mod (&2 pow dimindex(:N)))`,
  REPEAT GEN_TAC THEN MAP_EVERY (MP_TAC o C SPEC IVAL_VAL_CONG)
   [`x:N word`; `y:N word`; `word_sub x y:N word`] THEN
  MP_TAC(ISPECL [`x:N word`; `y:N word`] CONG_WORD_SUB) THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_ADD] THEN
  CONV_TAC INTEGER_RULE);;

let IWORD_INT_SUB = prove
 (`!x y. iword(x - y):N word = word_sub (iword x) (iword y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IVAL_CONG] THEN
  MP_TAC(ISPECL [`iword x:N word`; `iword y:N word`] ICONG_WORD_SUB) THEN
  MAP_EVERY (MP_TAC o C ISPEC IVAL_IWORD_CONG)
   [`x - y:int`; `y:int`; `x:int`] THEN
  CONV_TAC INTEGER_RULE);;

let WORD_SUB_IMODULAR = prove
 (`(word_sub:N word->N word->N word) = imodular ( - )`,
  REWRITE_TAC[FUN_EQ_THM; GSYM IVAL_CONG] THEN
  ASM_MESON_TAC[ICONG_WORD_SUB; CONG_IMODULAR; INTEGER_RULE
   `(a:int == b) (mod n) /\ (c == b) (mod n) ==> (a == c) (mod n)`]);;

let WORD_SUB = prove
 (`!x y. word(x - y):N word =
         if y <= x then word_sub (word x) (word y) else word 0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[WORD_IWORD; GSYM INT_OF_NUM_SUB; IWORD_INT_SUB];
    ASM_MESON_TAC[SUB_EQ_0; LE_CASES]]);;

let word_neg = new_definition
 `word_neg (a:N word) = word_sub (word 0) a`;;

let ODD_VAL_WORD_SUB = prove
 (`!x y:N word. ODD(val(word_sub x y)) <=> ~(ODD(val x) <=> ODD(val y))`,
  SIMP_TAC[VAL_WORD_SUB; ODD_MOD_EVEN; EVEN_EXP; ARITH; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[ODD_ADD; ODD_SUB; ODD_EXP; DIMINDEX_NONZERO; ARITH] THEN
  REWRITE_TAC[VAL_BOUND]);;

let EVEN_VAL_WORD_SUB = prove
 (`!x y:N word. EVEN(val(word_sub x y)) <=> (EVEN(val x) <=> EVEN(val y))`,
  REWRITE_TAC[GSYM NOT_ODD; ODD_VAL_WORD_SUB] THEN CONV_TAC TAUT);;

let VAL_WORD_NEG = prove
 (`!x:(N) word.
        val(word_neg x) =
        (2 EXP dimindex(:N) - val(x)) MOD (2 EXP dimindex(:N))`,
  REWRITE_TAC[word_neg; VAL_WORD_SUB; VAL_WORD_0; ADD_CLAUSES]);;

let VAL_WORD_NEG_CASES = prove
 (`!x:(N) word.
        val(word_neg x) =
        if val x = 0 then 0 else 2 EXP dimindex(:N) - val(x)`,
  REWRITE_TAC[word_neg; VAL_WORD_SUB_CASES; VAL_WORD_0] THEN
  SIMP_TAC[LE; ADD_CLAUSES; SUB_REFL]);;

let INT_VAL_WORD_NEG_CASES = prove
 (`!x:N word.
        &(val(word_neg x)):int =
        if &(val x):int = &0 then &0 else &2 pow dimindex(:N) - &(val x)`,
  SIMP_TAC[INT_OF_NUM_POW; INT_OF_NUM_SUB; LT_IMP_LE; VAL_BOUND] THEN
  REWRITE_TAC[VAL_WORD_NEG_CASES; INT_OF_NUM_EQ] THEN MESON_TAC[]);;

let REAL_VAL_WORD_NEG_CASES = prove
 (`!x:N word.
        &(val(word_neg x)):real =
        if &(val x):real = &0 then &0 else &2 pow dimindex(:N) - &(val x)`,
  SIMP_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_SUB; LT_IMP_LE; VAL_BOUND] THEN
  REWRITE_TAC[VAL_WORD_NEG_CASES; REAL_OF_NUM_EQ] THEN MESON_TAC[]);;

let INT_VAL_WORD_NEG = prove
 (`!x:N word. &(val(word_neg x)):int =
              &2 pow dimindex(:N) * &(bitval(~(x = word 0))) -
              &(val x)`,
  GEN_TAC THEN REWRITE_TAC[INT_VAL_WORD_NEG_CASES] THEN
  REWRITE_TAC[INT_OF_NUM_EQ; VAL_EQ_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_0] THEN
  INT_ARITH_TAC);;

let REAL_VAL_WORD_NEG = prove
 (`!x:N word. &(val(word_neg x)):real =
              &2 pow dimindex(:N) * &(bitval(~(x = word 0))) -
              &(val x)`,
  GEN_TAC THEN REWRITE_TAC[REAL_VAL_WORD_NEG_CASES] THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; VAL_EQ_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_0] THEN
  REAL_ARITH_TAC);;

let CONG_WORD_NEG = prove
 (`!x:(N)word.
        (val(word_neg x) + val x == 0) (mod (2 EXP dimindex(:N)))`,
  REWRITE_TAC[word_neg] THEN MESON_TAC[CONG_WORD_SUB; VAL_WORD_0]);;

let INT_CONG_WORD_NEG = prove
 (`!x:N word. (&(val(word_neg x)):int == -- &(val x))
              (mod (&2 pow dimindex(:N)))`,
  REWRITE_TAC[INTEGER_RULE
   `(z:int == --y) (mod n) <=> (z + y == &0) (mod n)`] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; CONG_WORD_NEG; GSYM num_congruent]);;

let ICONG_WORD_NEG = prove
 (`!x:(N)word.
        (ival(word_neg x) == --(ival x)) (mod (&2 pow dimindex(:N)))`,
  REWRITE_TAC[word_neg] THEN
  MESON_TAC[ICONG_WORD_SUB; INT_SUB_LZERO; IVAL_WORD_0]);;

let IWORD_INT_NEG = prove
 (`!x. iword(--x):N word = word_neg (iword x)`,
  REWRITE_TAC[GSYM INT_SUB_LZERO; word_neg] THEN
  REWRITE_TAC[IWORD_INT_SUB; GSYM WORD_IWORD]);;

let WORD_NEG_AS_ADD = prove
 (`!x:N word. word_neg x = word_add (word_not x) (word 1)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_CONG; CONG; VAL_WORD_NEG] THEN
  REWRITE_TAC[MOD_MOD_REFL; VAL_WORD_ADD; VAL_WORD_1; VAL_WORD_NOT] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  SIMP_TAC[VAL_BOUND; ARITH_RULE `n < e ==> (e - 1 - n) + 1 = e - n`]);;

let WORD_NOT_AS_SUB = prove
 (`!x:N word. word_not x = word_sub (word_neg x) (word 1)`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; CONG; VAL_WORD_SUB; VAL_WORD_NEG] THEN
  REWRITE_TAC[MOD_MOD_REFL; VAL_WORD_SUB; VAL_WORD_1; VAL_WORD_NOT] THEN
  CONV_TAC MOD_DOWN_CONV THEN SIMP_TAC[VAL_BOUND; ARITH_RULE
   `x < e ==> (e - x) + (e - 1) = e + (e - 1 - x)`] THEN
  REWRITE_TAC[GSYM CONG] THEN CONV_TAC NUMBER_RULE);;

let VAL_WORD_NEG_1 = prove
 (`val(word_neg(word 1:N word)) = 2 EXP dimindex(:N) - 1`,
  REWRITE_TAC[VAL_WORD_NEG_CASES; VAL_WORD_1; ARITH_EQ]);;

let IVAL_WORD_NEG_1 = prove
 (`ival(word_neg(word 1:N word)) = -- &1`,
  REWRITE_TAC[ival; VAL_WORD_NEG_1] THEN
  REWRITE_TAC[ARITH_RULE `m - 1 < n <=> ~(n = 0) /\ m <= n`] THEN
  SIMP_TAC[LE_EXP; EXP_EQ_0; ARITH_EQ; DIMINDEX_NONZERO;
           ARITH_RULE `n <= n - 1 <=> n = 0`;
           GSYM INT_OF_NUM_SUB; GSYM INT_OF_NUM_POW; LE_1] THEN
  INT_ARITH_TAC);;

let IVAL_EQ_MINUS1 = prove
 (`!w:N word. ival w = -- &1 <=> w = word_neg(word 1)`,
  REWRITE_TAC[GSYM IVAL_EQ; IVAL_WORD_NEG_1]);;

let WORD_NEG_1 = prove
 (`word_neg(word 1:N word) = word_not(word 0)`,
  REWRITE_TAC[WORD_NOT_AS_SUB; word_neg] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0; VAL_WORD_SUB_CASES] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ODD_VAL_WORD_NEG = prove
 (`!x:N word. ODD(val(word_neg x)) <=> ODD(val x)`,
  SIMP_TAC[VAL_WORD_NEG; ODD_MOD_EVEN; EVEN_EXP; ARITH; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[ODD_SUB; VAL_BOUND; ODD_EXP; DIMINDEX_NONZERO; ARITH]);;

let EVEN_VAL_WORD_NEG = prove
 (`!x:N word. EVEN(val(word_neg x)) <=> EVEN(val x)`,
  REWRITE_TAC[GSYM NOT_ODD; ODD_VAL_WORD_NEG] THEN CONV_TAC TAUT);;

let word_mul = new_definition
 `word_mul = modular ( * )`;;

let VAL_WORD_MUL = prove
 (`!x y:(N)word.
        val(word_mul x y) = (val(x) * val(y)) MOD (2 EXP dimindex(:N))`,
  REWRITE_TAC[word_mul; VAL_MODULAR]);;

let CONG_WORD_MUL = prove
 (`!x y:(N)word.
        (val(word_mul x y) == val x * val y) (mod (2 EXP dimindex(:N)))`,
  REWRITE_TAC[word_mul; CONG_MODULAR]);;

let INT_CONG_WORD_MUL = prove
 (`!x y:N word.
    (&(val(word_mul x y)):int == &(val x) * &(val y))
    (mod (&2 pow dimindex(:N)))`,
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent; CONG_WORD_MUL]);;

let WORD_MUL = prove
 (`!x y. word(x * y):N word = word_mul (word x) (word y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_CONG] THEN
  MP_TAC(ISPECL [`word x:N word`; `word y:N word`] CONG_WORD_MUL) THEN
  MAP_EVERY (MP_TAC o C ISPEC VAL_WORD_CONG)
   [`x * y:num`; `y:num`; `x:num`] THEN
  CONV_TAC NUMBER_RULE);;

let ICONG_WORD_MUL = prove
 (`!x y:(N)word.
        (ival(word_mul x y) == ival x * ival y) (mod (&2 pow dimindex(:N)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`x:N word`; `y:N word`] CONG_WORD_MUL) THEN
  MAP_EVERY (MP_TAC o C SPEC IVAL_VAL_CONG)
   [`x:N word`; `y:N word`; `word_mul x y:N word`] THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_MUL] THEN
  CONV_TAC INTEGER_RULE);;

let IWORD_INT_MUL = prove
 (`!x y. iword(x * y):N word = word_mul (iword x) (iword y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IVAL_CONG] THEN
  MP_TAC(ISPECL [`iword x:N word`; `iword y:N word`] ICONG_WORD_MUL) THEN
  MAP_EVERY (MP_TAC o C ISPEC IVAL_IWORD_CONG)
   [`x * y:int`; `y:int`; `x:int`] THEN
  CONV_TAC INTEGER_RULE);;

let WORD_MUL_IMODULAR = prove
 (`(word_mul:N word->N word->N word) = imodular ( * )`,
  REWRITE_TAC[FUN_EQ_THM; GSYM IVAL_CONG] THEN
  ASM_MESON_TAC[ICONG_WORD_MUL; CONG_IMODULAR; INTEGER_RULE
   `(a:int == b) (mod n) /\ (c == b) (mod n) ==> (a == c) (mod n)`]);;

let ODD_VAL_WORD_MUL = prove
 (`!x y:N word. ODD(val(word_mul x y)) <=> ODD(val x) /\ ODD(val y)`,
  SIMP_TAC[VAL_WORD_MUL; ODD_MOD_EVEN; EVEN_EXP; ARITH; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[ODD_MULT]);;

let EVEN_VAL_WORD_MUL = prove
 (`!x y:N word. EVEN(val(word_mul x y)) <=> EVEN(val x) \/ EVEN(val y)`,
  REWRITE_TAC[GSYM NOT_ODD; ODD_VAL_WORD_MUL] THEN CONV_TAC TAUT);;

let word_udiv = new_definition
 `word_udiv = modular (DIV)`;;

let VAL_WORD_UDIV = prove
 (`!x y:(N)word.
        val(word_udiv x y) = val(x) DIV val(y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_udiv; VAL_MODULAR] THEN
  MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC(ARITH_RULE
   `m DIV n <= m /\ m < p ==> m DIV n < p`) THEN
  REWRITE_TAC[VAL_BOUND; DIV_LE]);;

let word_umod = new_definition
 `word_umod = modular (MOD)`;;

let VAL_WORD_UMOD = prove
 (`!x y:(N)word.
        val(word_umod x y) = val(x) MOD val(y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_umod; VAL_MODULAR] THEN
  MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC(ARITH_RULE
   `m MOD n <= m /\ m < p ==> m MOD n < p`) THEN
  REWRITE_TAC[VAL_BOUND; MOD_LE]);;

let word_umax = new_definition
 `word_umax = modular (MAX)`;;

let word_imax = new_definition
 `word_imax = imodular (max)`;;

let VAL_WORD_UMAX = prove
 (`!x y:(N)word.
        val(word_umax x y) = MAX (val x) (val y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_umax; VAL_MODULAR] THEN
  MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[ARITH_RULE `MAX x y < n <=> x < n /\ y < n`] THEN
  REWRITE_TAC[VAL_BOUND]);;

let WORD_UMAX = prove
 (`!x y:N word. word_umax x y = if val x <= val y then y else x`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UMAX; MAX]);;

let WORD_UMAX_SYM = prove
 (`!x y:N word. word_umax x y = word_umax y x`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UMAX] THEN ARITH_TAC);;

let WORD_UMAX_ASSOC = prove
 (`!x y z:N word. word_umax x (word_umax y z) = word_umax (word_umax x y) z`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UMAX] THEN ARITH_TAC);;

let IVAL_WORD_IMAX = prove
 (`!x y:(N)word.
        ival(word_imax x y) = max (ival x) (ival y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_imax; imodular] THEN
  REWRITE_TAC[INT_MAX] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IWORD_IVAL]);;

let word_umin = new_definition
 `word_umin = modular (MIN)`;;

let word_imin = new_definition
 `word_imin = imodular (min)`;;

let VAL_WORD_UMIN = prove
 (`!x y:(N)word.
        val(word_umin x y) = MIN (val x) (val y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_umin; VAL_MODULAR] THEN
  MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[ARITH_RULE `MIN x y < n <=> x < n \/ y < n`] THEN
  REWRITE_TAC[VAL_BOUND]);;

let WORD_UMIN = prove
 (`!x y:N word. word_umin x y = if val x <= val y then x else y`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UMIN; MIN]);;

let WORD_UMIN_SYM = prove
 (`!x y:N word. word_umin x y = word_umin y x`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UMIN] THEN ARITH_TAC);;

let WORD_UMIN_ASSOC = prove
 (`!x y z:N word. word_umin x (word_umin y z) = word_umin (word_umin x y) z`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UMIN] THEN ARITH_TAC);;

let IVAL_WORD_IMIN = prove
 (`!x y:(N)word.
        ival(word_imin x y) = min (ival x) (ival y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_imin; imodular] THEN
  REWRITE_TAC[INT_MIN] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IWORD_IVAL]);;

let word_shl = new_definition
  `word_shl (x:(N)word) n = word((val x) * 2 EXP n):(N)word`;;

let VAL_WORD_SHL = prove
 (`!(x:N word) n.
        val(word_shl x n) = (2 EXP n * val x) MOD (2 EXP dimindex(:N))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_shl; VAL_WORD; MULT_SYM]);;

let CONG_WORD_SHL = prove
 (`!(x:N word) n.
        (val(word_shl x n) == 2 EXP n * val x) (mod (2 EXP dimindex(:N)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_SHL; CONG] THEN
  CONV_TAC MOD_DOWN_CONV THEN REFL_TAC);;

let ICONG_WORD_SHL = prove
 (`!(x:N word) n.
        (ival(word_shl x n) == &2 pow n * ival x) (mod (&2 pow dimindex(:N)))`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL [`x:N word`; `n:num`] CONG_WORD_SHL) THEN
  MAP_EVERY (MP_TAC o C SPEC IVAL_VAL_CONG)
   [`x:N word`; `word_shl x n:N word`] THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_MUL] THEN
  CONV_TAC INTEGER_RULE);;

let BIT_WORD_SHL = prove
 (`!(x:N word) n i.
        bit i (word_shl x n) <=>
        n <= i /\ i < dimindex(:N) /\ bit (i - n) x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `i < dimindex(:N)` THENL
   [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[bit]] THEN
  REWRITE_TAC[word_shl; BIT_VAL; VAL_WORD] THEN
  SUBGOAL_THEN `dimindex(:N) = i + (dimindex(:N) - i)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[EXP_ADD; GSYM DIV_MOD]] THEN
  ASM_SIMP_TAC[ODD_MOD_POW2; ARITH_RULE `i < n ==> ~(n - i = 0)`] THEN
  ASM_CASES_TAC `n:num <= i` THEN ASM_REWRITE_TAC[] THENL
   [AP_TERM_TAC THEN
    SUBGOAL_THEN `i:num = (i - n) + n`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th])
    THENL [ASM_ARITH_TAC; REWRITE_TAC[EXP_ADD]] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_MP_TAC DIV_MULT2 THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
    SUBGOAL_THEN `n:num = i + (n - i)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ONCE_REWRITE_TAC[MULT_SYM]] THEN
    REWRITE_TAC[EXP_ADD; GSYM MULT_ASSOC] THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ; EXP_EQ_0] THEN
    REWRITE_TAC[ODD_MULT; ODD_EXP] THEN ASM_ARITH_TAC]);;

let WORD_SHL_WORD_OF_BITS = prove
 (`!(x:N word) n.
        word_shl x n =
        word_of_bits {i | n <= i /\ i < dimindex(:N) /\ bit (i - n) x}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [WORD_OF_BITS_ALT] THEN
  AP_TERM_TAC THEN REWRITE_TAC[BIT_WORD_SHL] THEN SET_TAC[]);;

let WORD_SHL_0 = prove
 (`!n. word_shl (word 0:N word) n = word 0`,
  REWRITE_TAC[word_shl; VAL_WORD_0; MULT_CLAUSES]);;

let WORD_SHL_ZERO = prove
 (`!x:N word. word_shl x 0 = x`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; EXP; MULT_CLAUSES] THEN
  SIMP_TAC[MOD_LT; VAL_BOUND]);;

let WORD_SHL_TRIVIAL = prove
 (`!(x:N word) n.
       dimindex(:N) <= n ==> word_shl x n = word 0`,
  SIMP_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SHL; BIT_WORD_0] THEN ARITH_TAC);;

let WORD_SHL_COMPOSE = prove
 (`!(x:N word) m n. word_shl (word_shl x m) n = word_shl x (m + n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_shl; VAL_WORD; EXP_ADD] THEN
  REWRITE_TAC[WORD_EQ; CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[MULT_ASSOC]);;

let WORD_SHL_LSB_ALT = prove
 (`!x:N word.
        word_shl x (dimindex(:N) - 1) =
        if bit 0 x then word(2 EXP (dimindex(:N) - 1)) else word 0`,
  GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_0; BIT_WORD_POW2; BIT_WORD_SHL] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i = dimindex(:N) - 1` THEN
  ASM_REWRITE_TAC[SUB_REFL] THEN ASM_ARITH_TAC);;

let WORD_SHL_LSB = prove
 (`!x:N word.
        word_shl x (dimindex(:N) - 1) =
        word(2 EXP (dimindex(:N) - 1) * bitval(bit 0 x))`,
  GEN_TAC THEN REWRITE_TAC[WORD_SHL_LSB_ALT; bitval] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES]);;

let WORD_SHL_WORD = prove
 (`!x n. word_shl (word x:N word) n = word(2 EXP n * x)`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]);;

let WORD_SHL_AS_IWORD = prove
 (`!(x:N word) n. word_shl x n = iword(ival x * &2 pow n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_shl; WORD_IWORD] THEN
  REWRITE_TAC[IWORD_EQ; GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(a:int == b) (mod n) ==> (b * x == a * x) (mod n)`) THEN
  REWRITE_TAC[IVAL_VAL_CONG]);;

let WORD_SHL_IWORD = prove
 (`!x n. word_shl (iword x:N word) n = iword(&2 pow n * x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_SHL_AS_IWORD; IWORD_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(x:int == y) (mod p) ==> (x * n == n * y) (mod p)`) THEN
  REWRITE_TAC[IVAL_IWORD_CONG]);;

let WORD_MUL_EXPAND = prove
 (`!x y:N word.
        word_mul x y =
        word(nsum {i | i < dimindex(:N)}
                  (\i. bitval(bit i x) * val(word_shl y i)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_mul; modular] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [val_def] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; GSYM NSUM_RMUL; NUMSEG_LT_DIMINDEX] THEN
  ONCE_REWRITE_TAC[MOD_NSUM_MOD_NUMSEG] THEN
  REWRITE_TAC[VAL_WORD_SHL] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[MULT_AC]);;

let word_ushr = new_definition
  `word_ushr (x:(N)word) n =
        word((val x) DIV (2 EXP n)):(N)word`;;

let VAL_WORD_USHR = prove
 (`!(x:N word) n.
        val(word_ushr x n) = val x DIV (2 EXP n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_ushr; VAL_WORD] THEN
  MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC(ARITH_RULE
   `m DIV n <= m /\ m < p ==> m DIV n < p`) THEN
  REWRITE_TAC[VAL_BOUND; DIV_LE]);;

let WORD_USHR_EQ_0 = prove
 (`!(x:N word) n. word_ushr x n = word 0 <=> val x < 2 EXP n`,
  REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_USHR] THEN
  SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ]);;

let BIT_WORD_USHR = prove
 (`!(x:N word) n i.
        bit i (word_ushr x n) <=> bit (i + n) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_ushr; BIT_VAL; VAL_WORD] THEN
  REWRITE_TAC[DIV_MOD; DIV_DIV] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM EXP_ADD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN
  TRANS_TAC LTE_TRANS `2 EXP dimindex(:N)` THEN
  ASM_REWRITE_TAC[VAL_BOUND; LE_EXP; DIMINDEX_NONZERO] THEN
  ARITH_TAC);;

let WORD_USHR_WORD_OF_BITS = prove
 (`!(x:N word) n.
        word_ushr x n =
        word_of_bits {i | i < dimindex(:N) /\ bit (i + n) x}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [WORD_OF_BITS_ALT] THEN
  AP_TERM_TAC THEN REWRITE_TAC[BIT_WORD_USHR] THEN SET_TAC[]);;

let WORD_USHR_0 = prove
 (`!n. word_ushr (word 0:N word) n = word 0`,
  REWRITE_TAC[word_ushr; VAL_WORD_0; DIV_0]);;

let WORD_USHR_ZERO = prove
 (`!x:N word. word_ushr x 0 = x`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; EXP; DIV_1] THEN
  SIMP_TAC[MOD_LT; VAL_BOUND]);;

let WORD_USHR_COMPOSE = prove
 (`!(x:N word) m n. word_ushr (word_ushr x m) n = word_ushr x (m + n)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[word_ushr] THEN
  REWRITE_TAC[VAL_WORD_USHR] THEN REWRITE_TAC[EXP_ADD; DIV_DIV]);;

let WORD_USHR_MSB_ALT = prove
 (`!x:N word. word_ushr x (dimindex(:N) - 1) =
              if bit (dimindex(:N) - 1) x then word 1 else word 0`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BIT_WORD_0; BIT_WORD_1] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  MATCH_MP_TAC(REWRITE_RULE[] BIT_TRIVIAL) THEN ASM_ARITH_TAC);;

let WORD_USHR_MSB = prove
 (`!x:N word. word_ushr x (dimindex(:N) - 1) =
              word(bitval(bit (dimindex(:N) - 1) x))`,
  REWRITE_TAC[WORD_USHR_MSB_ALT; WORD_BITVAL]);;

let WORD_USHR_MSB_EQ = prove
 (`(!x:N word. word_ushr x (dimindex(:N) - 1) = word 1 <=>
               bit (dimindex(:N) - 1) x) /\
   (!x:N word. word_ushr x (dimindex(:N) - 1) = word 0 <=>
               ~bit (dimindex(:N) - 1) x) /\
   (!P (x:N word).
        (word_ushr x (dimindex(:N) - 1) = if P then word 1 else word 0) <=>
        (bit (dimindex(:N) - 1) x <=> P)) /\
   (!P (x:N word).
        (word_ushr x (dimindex(:N) - 1) = if P then word 0 else word 1) <=>
        (bit (dimindex(:N) - 1) x <=> ~P))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_USHR_MSB_ALT] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_NE_10]));;

let WORD_POPCOUNT_SHL = prove
 (`!(x:N word) n. word_popcount(word_shl x n) <= word_popcount x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_popcount] THEN
  TRANS_TAC LE_TRANS
   `CARD (IMAGE (\i. n + i) (bits_of_word (x:N word)))` THEN
  SIMP_TAC[CARD_IMAGE_LE; FINITE_BITS_OF_WORD] THEN
  MATCH_MP_TAC CARD_SUBSET THEN
  SIMP_TAC[SUBSET; FINITE_IMAGE; FINITE_BITS_OF_WORD] THEN
  REWRITE_TAC[IN_IMAGE; bits_of_word; IN_ELIM_THM; BIT_WORD_SHL] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN EXISTS_TAC `i - n:num` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let WORD_POPCOUNT_USHR = prove
 (`!(x:N word) n. word_popcount(word_ushr x n) <= word_popcount x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_popcount] THEN
  TRANS_TAC LE_TRANS
   `CARD (IMAGE (\i. i - n) (bits_of_word (x:N word)))` THEN
  SIMP_TAC[CARD_IMAGE_LE; FINITE_BITS_OF_WORD] THEN
  MATCH_MP_TAC CARD_SUBSET THEN
  SIMP_TAC[SUBSET; FINITE_IMAGE; FINITE_BITS_OF_WORD] THEN
  REWRITE_TAC[IN_IMAGE; bits_of_word; IN_ELIM_THM; BIT_WORD_USHR] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN EXISTS_TAC `i + n:num` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let word_ishr = new_definition
  `(word_ishr:N word ->num->N word) x n = iword((ival x) div (&2 pow n))`;;

let IVAL_WORD_ISHR = prove
 (`!(x:N word) n. ival(word_ishr x n) = (ival x) div (&2 pow n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_ishr] THEN
  MATCH_MP_TAC IVAL_IWORD THEN
  SIMP_TAC[INT_LE_DIV_EQ; INT_DIV_LT_EQ; INT_LT_POW2] THEN
  MP_TAC(ISPEC `x:N word` IVAL_BOUND) THEN
  MATCH_MP_TAC(INT_ARITH
   `&1 * a:int <= t * a
    ==> --a <= x /\ x < a ==> t * --a <= x /\ x < t * a`) THEN
  MATCH_MP_TAC INT_LE_RMUL THEN
  SIMP_TAC[INT_LE_POW2; INT_LT_IMP_LE; INT_LT_POW2]);;

let WORD_ISHR_EQ_0 = prove
 (`!(x:N word) n.
        word_ishr x n = word 0 <=> &0 <= ival x /\ ival x < &2 pow n`,
  REWRITE_TAC[GSYM IVAL_EQ_0; IVAL_WORD_ISHR] THEN
  SIMP_TAC[INT_DIV_EQ_0; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[INT_ABS_POW; INT_ABS_NUM]);;

let BIT_WORD_ISHR = prove
 (`!(w:N word) n i.
        bit i (word_ishr w n) <=>
        if i + n < dimindex(:N) then bit (i + n) w
        else i < dimindex(:N) /\ bit (dimindex(:N) - 1) w`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `i < dimindex(:N)` THENL
   [ALL_TAC; ASM_REWRITE_TAC[BIT_IVAL] THEN ASM_ARITH_TAC] THEN
  ASM_REWRITE_TAC[word_ishr; BIT_IWORD] THEN
  SIMP_TAC[INT_DIV_DIV; INT_POW_LE; INT_POS] THEN
  ONCE_REWRITE_TAC[INT_MUL_SYM] THEN REWRITE_TAC[GSYM INT_POW_ADD] THEN
  COND_CASES_TAC THENL [ASM_SIMP_TAC[BIT_IVAL]; ALL_TAC] THEN
  REWRITE_TAC[MSB_IVAL; GSYM INT_NOT_LE] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `--(&2 pow (i + n)) <= ival(w:N word) /\ ival w < &2 pow (i + n)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `w:N word` IVAL_BOUND) THEN MATCH_MP_TAC(INT_ARITH
     `a:int <= b ==> --a <= x /\ x < a ==> --b <= x /\ x < b`) THEN
    MATCH_MP_TAC INT_POW_MONO THEN REWRITE_TAC[INT_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ival(w:N word)`; `(&2:int) pow (i + n)`]
        INT_DIV_EQ_0) THEN
  ASM_REWRITE_TAC[INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ; INT_ABS_POW;
                  INT_ABS_NUM] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `-- &1 <= ival(w:N word) div &2 pow (i + n) /\
    ival(w:N word) div &2 pow (i + n) < &1`
  MP_TAC THENL
   [ASM_SIMP_TAC[INT_DIV_LT_EQ; INT_LE_DIV_EQ; INT_LT_POW2] THEN
    ASM_REWRITE_TAC[INT_MUL_RNEG; INT_MUL_RID];
    REWRITE_TAC[INT_ARITH
     `-- &1:int <= x /\ x < &1 <=> x = -- &1 \/ x = &0`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[INTEGER_RULE `(p:int) divides &0`] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[INTEGER_RULE `(x:int) divides --y <=> x divides y`] THEN
    REWRITE_TAC[GSYM num_divides; divides; GSYM EVEN_EXISTS] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let WORD_ISHR_WORD_OF_BITS = prove
 (`!(x:N word) n.
        word_ishr x n =
        word_of_bits {i | if i < dimindex(:N) - n then bit (i + n) x
                          else bit (dimindex(:N) - 1) x}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [WORD_OF_BITS_ALT] THEN
  REWRITE_TAC[WORD_OF_BITS_EQ] THEN X_GEN_TAC `i:num` THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM; BIT_WORD_ISHR] THEN
  REWRITE_TAC[ARITH_RULE `i + n:num < m <=> i < m - n`]);;

let WORD_ISHR_0 = prove
 (`!n. word_ishr (word 0:N word) n = word 0`,
  REWRITE_TAC[word_ishr; IVAL_WORD_0; INT_DIV_ZERO; GSYM WORD_IWORD]);;

let WORD_ISHR_ZERO = prove
 (`!x:N word. word_ishr x 0 = x`,
  REWRITE_TAC[GSYM IVAL_EQ; IVAL_WORD_ISHR; INT_POW; INT_DIV_1]);;

let WORD_ISHR_COMPOSE = prove
 (`!(x:N word) m n. word_ishr (word_ishr x m) n = word_ishr x (m + n)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[word_ishr] THEN
  REWRITE_TAC[IVAL_WORD_ISHR; INT_POW_ADD] THEN
  SIMP_TAC[INT_DIV_DIV; INT_POW_LE; INT_POS]);;

let WORD_ISHR_UNIQUE = prove
 (`!(x:N word) y n. ival x = &2 pow n * y ==> word_ishr x n = iword y`,
  SIMP_TAC[word_ishr; INT_DIV_MUL; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ]);;

let IVAL_WORD_ISHR_SHL_UNIQUE = prove
 (`!n (x:N word) y.
        ival(word_ishr (word_shl x n) n) = y <=>
        ival(word_shl x n) = &2 pow n * y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IVAL_WORD_ISHR] THEN
  SUBGOAL_THEN `&2 pow n divides ival(word_shl x n:N word)` MP_TAC THENL
   [DISJ_CASES_TAC(ARITH_RULE `dimindex(:N) <= n \/ n <= dimindex(:N)`) THEN
    ASM_SIMP_TAC[WORD_SHL_TRIVIAL; WORD_ISHR_0; IVAL_WORD_0;
                 INTEGER_RULE `(d:int) divides &0`] THEN
    ASM_SIMP_TAC[WORD_SHL_AS_IWORD; INT_DIVIDES_IVAL_IWORD] THEN
    CONV_TAC INTEGER_RULE;
    REWRITE_TAC[int_divides] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[INT_DIV_MUL; INT_POW_EQ_0; ARITH_EQ; INT_OF_NUM_EQ;
                 INT_EQ_MUL_LCANCEL]]);;

let word_ror = new_definition
 `(word_ror:N word->num->N word) w n =
        word_of_bits {i | bit ((i + n) MOD dimindex(:N)) w}`;;

let word_rol = new_definition
 `(word_rol:N word->num->N word) w n =
        word_of_bits {i | bit (num_of_int((&i - &n) rem &(dimindex(:N)))) w}`;;

let WORD_ROR_ROL_GEN = prove
 (`!(w:N word) n.
        word_ror w n = word_rol w (dimindex(:N) - n MOD dimindex(:N))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ror; word_rol; WORD_OF_BITS_EQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INT_OF_NUM_OF_INT o rand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[INT_DIVISION; DIMINDEX_NONZERO; INT_OF_NUM_EQ];
    DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE; DIVISION; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_ADD; INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(k:int == n) (mod d)
    ==> (i + n == i - (d - k)) (mod d)`) THEN
  REWRITE_TAC[INT_REM_MOD_SELF]);;

let WORD_ROL_ROR_GEN = prove
 (`!(w:N word) n.
        word_rol w n = word_ror w (dimindex(:N) - n MOD dimindex(:N))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ror; word_rol; WORD_OF_BITS_EQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INT_OF_NUM_OF_INT o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[INT_DIVISION; DIMINDEX_NONZERO; INT_OF_NUM_EQ];
    DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE; DIVISION; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; INT_REM_EQ; GSYM INT_OF_NUM_ADD] THEN
  SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE; DIVISION; DIMINDEX_NONZERO] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(k:int == n) (mod d)
    ==> (i - n == i + (d - k)) (mod d)`) THEN
  REWRITE_TAC[CONG_LMOD; INT_OF_NUM_REM; GSYM num_congruent] THEN
  CONV_TAC NUMBER_RULE);;

let WORD_ROR_PERIODIC = prove
 (`!(w:N word) m n.
        (m == n) (mod dimindex(:N)) ==> word_ror w m = word_ror w n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ror] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (NUMBER_RULE
   `(m == n) (mod d) ==> !i:num. (i + m == i + n) (mod d)`)) THEN
  SIMP_TAC[CONG]);;

let WORD_ROR_MOD = prove
 (`!(w:N word) n. word_ror w n = word_ror w (n MOD dimindex(:N))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC WORD_ROR_PERIODIC THEN
  REWRITE_TAC[CONG_RMOD] THEN CONV_TAC NUMBER_RULE);;

let WORD_ROR_EQ_SELF = prove
 (`!(w:N word) n. dimindex(:N) divides n ==> word_ror w n = w`,
  SIMP_TAC[divides; LEFT_IMP_EXISTS_THM; word_ror] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `i + d * n:num = n * d + i`] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOD_MULT_ADD] THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_OF_BITS] THEN X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_SIMP_TAC[MOD_LT; IN_ELIM_THM] THEN
  ASM_MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let WORD_ROR_ZERO = prove
 (`!w:N word. word_ror w 0 = w`,
  GEN_TAC THEN MATCH_MP_TAC WORD_ROR_EQ_SELF THEN CONV_TAC NUMBER_RULE);;

let WORD_ROL_PERIODIC = prove
 (`!(w:N word) m n.
        (m == n) (mod dimindex(:N)) ==> word_rol w m = word_rol w n`,
  SIMP_TAC[CONG; WORD_ROL_ROR_GEN]);;

let WORD_ROL_MOD = prove
 (`!(w:N word) n. word_rol w n = word_rol w (n MOD dimindex(:N))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC WORD_ROL_PERIODIC THEN
  REWRITE_TAC[CONG_RMOD] THEN CONV_TAC NUMBER_RULE);;

let WORD_ROL_EQ_SELF = prove
 (`!(w:N word) n. dimindex(:N) divides n ==> word_rol w n = w`,
  REWRITE_TAC[divides] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  SIMP_TAC[GSYM MOD_EQ_0; WORD_ROL_ROR_GEN; SUB_0] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WORD_ROR_EQ_SELF THEN
  CONV_TAC NUMBER_RULE);;

let WORD_ROL_ZERO = prove
 (`!w:N word. word_rol w 0 = w`,
  GEN_TAC THEN MATCH_MP_TAC WORD_ROL_EQ_SELF THEN CONV_TAC NUMBER_RULE);;

let WORD_ROR_ROL = prove
 (`!(w:N word) n.
        n <= dimindex(:N) ==> word_ror w n = word_rol w (dimindex(:N) - n)`,
  REWRITE_TAC[LE_LT] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WORD_ROR_ROL_GEN; MOD_LT; MOD_REFL; SUB_0; SUB_REFL] THEN
  MATCH_MP_TAC WORD_ROL_PERIODIC THEN CONV_TAC NUMBER_RULE);;

let WORD_ROL_ROR = prove
 (`!(w:N word) n.
        n <= dimindex(:N) ==> word_rol w n = word_ror w (dimindex(:N) - n)`,
  REWRITE_TAC[LE_LT] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WORD_ROL_ROR_GEN; MOD_LT; MOD_REFL; SUB_0; SUB_REFL] THEN
  MATCH_MP_TAC WORD_ROR_PERIODIC THEN CONV_TAC NUMBER_RULE);;

let WORD_ROR_SHIFTS = prove
 (`!(w:N word) n.
        n <= dimindex(:N)
        ==> word_ror w n =
            word_or (word_ushr w n) (word_shl w (dimindex(:N) - n))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ror] THEN
  SIMP_TAC[WORD_EQ_BITS; BIT_WORD_OF_BITS; BIT_WORD_OR] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i < dimindex(:N)` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; BIT_WORD_USHR; BIT_WORD_SHL] THEN
  REWRITE_TAC[ARITH_RULE `d - n <= i <=> ~(i + n:num < d)`] THEN
  ASM_CASES_TAC `i + n < dimindex(:N)` THEN ASM_SIMP_TAC[MOD_LT] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN ASM_SIMP_TAC[BIT_TRIVIAL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN
  EXISTS_TAC `1` THEN ASM_ARITH_TAC);;

let WORD_ROL_SHIFTS = prove
 (`!(w:N word) n.
        n <= dimindex(:N)
        ==> word_rol w n =
            word_or (word_shl w n) (word_ushr w (dimindex(:N) - n))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WORD_ROL_ROR] THEN
  ASM_SIMP_TAC[WORD_ROR_SHIFTS; ARITH_RULE `n - m:num <= n`] THEN
  ASM_SIMP_TAC[ARITH_RULE `m:num <= n ==> n - (n - m) = m`] THEN
  SIMP_TAC[WORD_EQ_BITS; BIT_WORD_OR; DISJ_SYM]);;

let BIT_WORD_ROR = prove
 (`!(w:N word) n i.
        bit i (word_ror w n) =
        if i + n MOD dimindex(:N) < dimindex(:N)
        then bit (i + n MOD dimindex(:N)) w
        else i < dimindex(:N) /\
             bit ((i + n MOD dimindex(:N)) - dimindex(:N)) w`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[WORD_ROR_MOD] THEN
  SIMP_TAC[WORD_ROR_SHIFTS; MOD_LT_EQ; LT_IMP_LE; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_USHR] THEN
  COND_CASES_TAC THENL
   [ASM_CASES_TAC `bit (i + n MOD dimindex(:N)) (w:N word)` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `~p /\ q /\ (r <=> r') ==> (p \/ q /\ r <=> r')`) THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[BIT_TRIVIAL; GSYM NOT_LT];
      ASM_ARITH_TAC;
      AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]]);;

let BIT_WORD_ROL = prove
 (`!(w:N word) n i.
        bit i (word_rol w n) =
        if i < n MOD dimindex(:N)
        then bit (i + (dimindex(:N) - n MOD dimindex(:N))) w
        else i < dimindex(:N) /\ bit (i - n MOD dimindex(:N)) w`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[WORD_ROL_MOD] THEN
  SIMP_TAC[WORD_ROL_SHIFTS; MOD_LT_EQ; LT_IMP_LE; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_USHR] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LT] THENL
   [MATCH_MP_TAC(TAUT `p ==> (p /\ q <=> q)`) THEN
    TRANS_TAC LT_TRANS `n MOD dimindex(:N)` THEN
    ASM_REWRITE_TAC[MOD_LT_EQ; DIMINDEX_NONZERO];
    ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(q <=> F) ==> (p \/ q <=> p)`) THEN
    MATCH_MP_TAC BIT_TRIVIAL THEN ASM_ARITH_TAC]);;

let WORD_ROR_COMPOSE = prove
 (`!(x:N word) m n. word_ror (word_ror x m) n = word_ror x (m + n)`,
  REWRITE_TAC[word_ror; BIT_WORD_OF_BITS; IN_ELIM_THM] THEN
  SIMP_TAC[MOD_LT_EQ; DIMINDEX_NONZERO] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[ADD_AC]);;

let WORD_ROL_COMPOSE = prove
 (`!(x:N word) m n. word_rol (word_rol x m) n = word_rol x (m + n)`,
  REWRITE_TAC[WORD_ROL_ROR_GEN; WORD_ROR_COMPOSE] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC WORD_ROR_PERIODIC THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_ADD] THEN
  SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE; MOD_LT_EQ; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[INTEGER_RULE
   `((n - a) + (n - b):int == (n - c)) (mod n) <=> (a + b == c) (mod n)`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; GSYM num_congruent; CONG] THEN
  CONV_TAC MOD_DOWN_CONV THEN REFL_TAC);;

let VAL_WORD_ROR = prove
 (`!(w:N word) k.
     k <= dimindex(:N)
     ==> val(word_ror w k) =
         2 EXP (dimindex(:N) - k) * val w MOD 2 EXP k + val w DIV 2 EXP k`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [ADD_SYM] THEN
  ASM_SIMP_TAC[WORD_ROR_SHIFTS] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_OR_DISJOINT o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
    SIMP_TAC[BIT_WORD_AND; BIT_WORD_USHR; BIT_WORD_SHL; BIT_WORD_0] THEN
    REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP(MESON[BIT_TRIVIAL; NOT_LE]
     `bit i (w:N word) ==> i < dimindex(:N)`))) THEN
    ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_SHL] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM MOD_MULT2; GSYM EXP_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let VAL_WORD_ROL = prove
 (`!(w:N word) k.
        k <= dimindex(:N)
        ==> val(word_rol w k) =
            2 EXP k * val w MOD 2 EXP (dimindex(:N) - k) +
            val w DIV 2 EXP (dimindex(:N) - k)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WORD_ROL_ROR] THEN
  SIMP_TAC[VAL_WORD_ROR; ARITH_RULE `n - m:num <= n`] THEN
  ASM_SIMP_TAC[ARITH_RULE `k:num <= n ==> n - (n - k) = k`]);;

let word_ule = new_definition `word_ule = relational2 (<=)`;;
let word_uge = new_definition `word_uge = relational2 (>=)`;;
let word_ult = new_definition `word_ult = relational2 (<)`;;
let word_ugt = new_definition `word_ugt = relational2 (>)`;;

let word_ile = new_definition `word_ile = irelational2 (<=)`;;
let word_ige = new_definition `word_ige = irelational2 (>=)`;;
let word_ilt = new_definition `word_ilt = irelational2 (<)`;;
let word_igt = new_definition `word_igt = irelational2 (>)`;;

let WORD_ULT = prove
 (`!x y:N word. word_ult x y <=> val x < val y`,
  REWRITE_TAC[word_ult; relational2]);;

let WORD_ULE = prove
 (`!x y:N word. word_ule x y <=> val x <= val y`,
  REWRITE_TAC[word_ule; relational2]);;

let WORD_UGT = prove
 (`!x y:N word. word_ugt x y <=> val x > val y`,
  REWRITE_TAC[word_ugt; relational2]);;

let WORD_UGE = prove
 (`!x y:N word. word_uge x y <=> val x >= val y`,
  REWRITE_TAC[word_uge; relational2]);;

let WORD_ILT = prove
 (`!x y:N word. word_ilt x y <=> ival x < ival y`,
  REWRITE_TAC[word_ilt; irelational2]);;

let WORD_ILE = prove
 (`!x y:N word. word_ile x y <=> ival x <= ival y`,
  REWRITE_TAC[word_ile; irelational2]);;

let WORD_IGT = prove
 (`!x y:N word. word_igt x y <=> ival x > ival y`,
  REWRITE_TAC[word_igt; irelational2]);;

let WORD_IGE = prove
 (`!x y:N word. word_ige x y <=> ival x >= ival y`,
  REWRITE_TAC[word_ige; irelational2]);;

(* ------------------------------------------------------------------------- *)
(* Simple "propagate value modulo" decision procedure.                       *)
(* ------------------------------------------------------------------------- *)

let WORD_VAL_CONG_CONV =
  let VAL_WORD_ADD_REM = prove
   (`!x y:N word.
          &(val(word_add x y)) rem (&2 pow dimindex(:N)) =
          ((&(val x) rem (&2 pow dimindex(:N))) +
           (&(val y) rem (&2 pow dimindex(:N)))) rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] INT_CONG_WORD_ADD] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[])
  and VAL_WORD_SUB_REM = prove
   (`!x y:N word.
          &(val(word_sub x y)) rem (&2 pow dimindex(:N)) =
          ((&(val x) rem (&2 pow dimindex(:N))) -
           (&(val y) rem (&2 pow dimindex(:N)))) rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] INT_CONG_WORD_SUB] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[])
  and VAL_WORD_NEG_REM = prove
   (`!x:N word.
          &(val(word_neg x)) rem (&2 pow dimindex(:N)) =
          (--(&(val x) rem (&2 pow dimindex(:N)))) rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] INT_CONG_WORD_NEG] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[])
  and VAL_WORD_NOT_REM = prove
   (`!x:N word.
          &(val(word_not x)) rem (&2 pow dimindex(:N)) =
          (--(&(val x) rem (&2 pow dimindex(:N)) + &1))
          rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[INT_VAL_WORD_NOT] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN
    REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE)
  and VAL_WORD_MUL_REM = prove
   (`!x y:N word.
          &(val(word_mul x y)) rem (&2 pow dimindex(:N)) =
          ((&(val x) rem (&2 pow dimindex(:N))) *
           (&(val y) rem (&2 pow dimindex(:N)))) rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] INT_CONG_WORD_MUL] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[])
  and VAL_IWORD_REM = prove
   (`!x. &(val(iword x:N word)) rem (&2 pow dimindex(:N)) =
         x rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[INT_REM_EQ; VAL_IWORD_CONG])
  and VAL_WORD_REM = prove
   (`!n. &(val(word n:N word)) rem (&2 pow dimindex(:N)) =
         &n rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[VAL_WORD; INT_OF_NUM_REM; INT_OF_NUM_POW] THEN
    REWRITE_TAC[MOD_MOD_REFL])
  and VAL_WORD_SHL_REM = prove
   (`!(x:N word) n.
      &(val(word_shl x n)) rem (&2 pow dimindex(:N)) =
      (&2 pow n * &(val x) rem (&2 pow dimindex(:N)))
      rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
    REWRITE_TAC[VAL_WORD_SHL] THEN CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[])
  and INT_OF_NUMOP_REM = prove
   (`&(x + y) rem (&2 pow dimindex(:N)) =
     (&x rem (&2 pow dimindex(:N)) +
      &y rem (&2 pow dimindex(:N))) rem (&2 pow dimindex(:N)) /\
     &(x * y) rem (&2 pow dimindex(:N)) =
     (&x rem (&2 pow dimindex(:N)) *
      &y rem (&2 pow dimindex(:N))) rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[])
  and INT_OF_INTOP_REM = prove
   (`(x + y) rem (&2 pow dimindex(:N)) =
     (x rem (&2 pow dimindex(:N)) +
      y rem (&2 pow dimindex(:N))) rem (&2 pow dimindex(:N)) /\
     (x - y) rem (&2 pow dimindex(:N)) =
     (x rem (&2 pow dimindex(:N)) -
      y rem (&2 pow dimindex(:N))) rem (&2 pow dimindex(:N)) /\
     (x * y) rem (&2 pow dimindex(:N)) =
     (x rem (&2 pow dimindex(:N)) *
      y rem (&2 pow dimindex(:N))) rem (&2 pow dimindex(:N))`,
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[])
  and INT_OF_NEG_REM = prove
   (`(--x) rem (&2 pow dimindex(:N)) =
     (--(x rem (&2 pow dimindex(:N)))) rem (&2 pow dimindex(:N))`,
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[])
  and INT_REM_REM_REFL = prove
   (`(x rem (&2 pow dimindex(:N))) rem (&2 pow dimindex(:N)) =
     x rem (&2 pow dimindex(:N))`,
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[])
  and IVAL_VAL_REM = prove
   (`!x:N word. ival x rem (&2 pow dimindex(:N)) =
                &(val x) rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[INT_REM_EQ; IVAL_VAL_CONG])
  and topth = prove
   (`(!v w:N word.
          v = w <=>
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N))) /\
     (!(v:N word) (w:N word).
          val v = val w <=>
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N))) /\
     (!(v:N word) (w:N word).
          val v MOD 2 EXP dimindex(:N) = val w MOD 2 EXP dimindex(:N) <=>
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N))) /\
     (!(v:N word) (w:N word).
          (val v == val w) (mod (2 EXP dimindex(:N))) <=>
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N))) /\
     (!(v:N word) (w:N word).
          &(val v):int = &(val w) <=>
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N))) /\
     (!(v:N word) (w:N word).
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N)) <=>
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N))) /\
     (!(v:N word) (w:N word).
          (&(val v):int == &(val w)) (mod (&2 pow dimindex(:N))) <=>
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N))) /\
     (!(v:N word) (w:N word).
          ival v = ival w <=>
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N))) /\
     (!(v:N word) (w:N word).
          ival v rem (&2 pow dimindex(:N)) =
          ival w rem (&2 pow dimindex(:N)) <=>
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N))) /\
     (!(v:N word) (w:N word).
          (ival v == ival w) (mod (&2 pow dimindex(:N))) <=>
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N)))`,
    REWRITE_TAC[IVAL_EQ; IVAL_CONG;
                REWRITE_RULE[GSYM INT_REM_EQ] IVAL_CONG] THEN
    REWRITE_TAC[CONG; GSYM INT_REM_EQ; GSYM VAL_EQ] THEN
    ONCE_REWRITE_TAC[GSYM VAL_MOD_REFL] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]) in
  let conv_special = GEN_REWRITE_CONV I [VAL_WORD_NOT_REM]
  and conv_unary = GEN_REWRITE_CONV I
   [VAL_WORD_NEG_REM; INT_OF_NEG_REM; VAL_WORD_SHL_REM]
  and conv_binary = GEN_REWRITE_CONV I
   [VAL_WORD_ADD_REM; VAL_WORD_SUB_REM; VAL_WORD_MUL_REM;
    INT_OF_NUMOP_REM; INT_OF_INTOP_REM]
  and conv_self = GEN_REWRITE_CONV I
   [VAL_IWORD_REM; VAL_WORD_REM; IVAL_VAL_REM; INT_REM_REM_REFL] in
  let rec conv tm =
    ((conv_special THENC LAND_CONV (RAND_CONV(LAND_CONV conv))) ORELSEC
     (conv_unary THENC LAND_CONV (RAND_CONV conv)) ORELSEC
     (conv_binary THENC LAND_CONV (BINOP_CONV conv)) ORELSEC
     (conv_self THENC conv) ORELSEC
     SUB_CONV conv ORELSEC REFL) tm in
  GEN_REWRITE_CONV I [topth] THENC
  conv THENC
  INT_REM_DOWN_CONV THENC
  GEN_REWRITE_CONV I [INT_REM_EQ];;

let WORD_RULE =
  let soppify = striplist (dest_binop `(+):int->int->int`)
  and pth = prove
   (`!k. (x == &0) (mod (&2 pow dimindex(:N))) <=>
         (--k * &(val(word_not(word 0:N word))) + (x - k):int == &0)
         (mod (&2 pow dimindex(:N)))`,
    REWRITE_TAC[INT_VAL_WORD_NOT; VAL_WORD_0] THEN
    CONV_TAC INTEGER_RULE) in
  let WORD_UNBLAST_TAC =
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    TRY(GEN_REWRITE_TAC I
         [INTEGER_RULE `(x:int == y) (mod n) <=> (x - y == &0) (mod n)`] THEN
        CONV_TAC(RATOR_CONV(LAND_CONV INT_POLY_CONV)) THEN
        W(fun (asl,w) ->
          match filter is_intconst (soppify(lhand(rator w)))
          with [c] -> GEN_REWRITE_TAC I [SPEC c pth] THEN
                      CONV_TAC(RATOR_CONV(LAND_CONV INT_POLY_CONV))
             | _ -> ALL_TAC) THEN
        GEN_REWRITE_TAC I [GSYM INT_REM_EQ] THEN
        AP_THM_TAC THEN AP_TERM_TAC) THEN
    REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
    CONV_TAC(LAND_CONV REAL_POLY_CONV) THEN
    REWRITE_TAC[VAL; REAL_OF_NUM_SUM_NUMSEG] THEN
    REWRITE_TAC[GSYM SUM_ADD_NUMSEG; GSYM SUM_SUB_NUMSEG;
                GSYM SUM_LMUL; GSYM SUM_RMUL; GSYM SUM_NEG] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_SUB_RZERO] THEN
    MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `i <= n - 1 ==> ~(n = 0) ==> i < n`)) THEN
    REWRITE_TAC[DIMINDEX_NONZERO] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[BIT_WORD_AND_ALT; BIT_WORD_XOR_ALT; BIT_WORD_OR_ALT;
                    BIT_WORD_NOT; BIT_WORD_0] THEN
    REWRITE_TAC[INT_BITVAL_AND; INT_BITVAL_OR; INT_BITVAL_NOT;
                INT_BITVAL_IMP; INT_BITVAL_IFF; BITVAL_CLAUSES] THEN
    GEN_REWRITE_TAC I [GSYM INT_SUB_0] THEN
    CONV_TAC(LAND_CONV BINT_POLY_CONV) THEN REWRITE_TAC[] THEN NO_TAC in
  let wordprover tm =
    try NUMBER_RULE tm with Failure _ -> prove(tm,WORD_UNBLAST_TAC) in
  fun tm ->
    try
      let avs,bod = strip_forall tm in
      let th = ONCE_DEPTH_CONV WORD_VAL_CONG_CONV bod in
      GENL avs (EQT_ELIM(TRANS th (EQT_INTRO(wordprover (rand(concl th))))))
    with Failure m ->
      failwith ("WORD_RULE `" ^ (string_of_term tm) ^ "`: " ^ m);;

(* ------------------------------------------------------------------------- *)
(* A somewhat complementary purely bitwise decision procedure.               *)
(* ------------------------------------------------------------------------- *)

let WORD_BITWISE_TAC =
  let WORD_BITWISE_CONV =
    GEN_REWRITE_CONV I [WORD_EQ_BITS_ALT] THENC
    GEN_REWRITE_CONV (BINDER_CONV o RAND_CONV o BINOP_CONV o TOP_DEPTH_CONV)
     [BIT_WORD_NOT; BIT_WORD_AND; BIT_WORD_OR;
      BIT_WORD_XOR; BIT_WORD_OF_BITS; BIT_WORD_0;
      IN_INSERT; NOT_IN_EMPTY; IN_UNIV] in
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_BITWISE_CONV) THEN
  GEN_REWRITE_TAC DEPTH_CONV
   [MESON[] `(!i. i < dimindex(:N) ==> P i) /\
             (!i. i < dimindex(:N) ==> Q i) <=>
             (!i. i < dimindex(:N) ==> P i /\ Q i)`] THEN
  TRY(MATCH_MP_TAC(MESON[]
       `(!i. i < dimindex(:N) ==> P i ==> Q i)
        ==> (!i. i < dimindex(:N) ==> P i)
             ==> (!i. i < dimindex(:N) ==> Q i)`) ORELSE
      MATCH_MP_TAC(MESON[]
       `(!i. i < dimindex(:N) ==> (P i <=> Q i))
        ==> ((!i. i < dimindex(:N) ==> P i) <=>
             (!i. i < dimindex(:N) ==> Q i))`)) THEN
  TRY(GEN_TAC THEN DISCH_TAC) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC TAUT;;

let WORD_BITWISE_RULE tm =
  try
    prove(tm,WORD_BITWISE_TAC)
  with Failure m ->
    failwith ("WORD_BITWISE_RULE `" ^ (string_of_term tm) ^ "`: " ^ m);;

let WORD_BITWISE_TAC = CONV_TAC WORD_BITWISE_RULE;;

(* ------------------------------------------------------------------------- *)
(* Slightly ad hoc but useful reduction to linear arithmetic.                *)
(* ------------------------------------------------------------------------- *)

let WORD_ARITH_TAC =
  let msb_pth = prove
   (`dimindex (:N) - 1 < dimindex(:N)`,
    REWRITE_TAC[DIMINDEX_GE_1; ARITH_RULE `n - 1 < n <=> 1 <= n`])
  and wordy tm =
    match tm with Var(_,Tyapp("word",[_])) -> true | _ -> false in
  REPEAT(CONJ_TAC ORELSE GEN_TAC) THEN REWRITE_TAC[WORD_USHR_MSB_EQ] THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_AND; BIT_WORD_NOT; BIT_WORD_XOR;
              BIT_WORD_INT_MIN; BIT_WORD_1; BIT_WORD_0; msb_pth] THEN
  REWRITE_TAC[MSB_INT_VAL; WORD_NOT_AS_SUB; WORD_RULE
   `word_shl (x:N word) 1 = word_add x x`] THEN
  REWRITE_TAC[WORD_ULT; WORD_ULE; WORD_UGT; WORD_UGE;
              WORD_ILT; WORD_ILE; WORD_IGT; WORD_IGE] THEN
  REWRITE_TAC[irelational2; relational2; GSYM VAL_EQ; INT_IVAL; WORD_VAL;
              GSYM WORD_MUL; GSYM WORD_ADD; VAL_WORD] THEN
  REWRITE_TAC[INT_GT; INT_GE; GT; GE] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM] THEN
  REWRITE_TAC[INT_VAL_WORD_NEG_CASES; INT_VAL_WORD_ADD_CASES;
              INT_VAL_WORD_INT_MIN;
              INT_VAL_WORD_SUB_CASES; INT_IVAL; VAL_WORD_0; VAL_WORD_1] THEN
  REWRITE_TAC[VAL_WORD; GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  W(MAP_EVERY (MP_TAC o C ISPEC INT_VAL_BOUND) o find_terms wordy o snd) THEN
  REWRITE_TAC[CONJUNCT2 TWICE_MSB] THEN CONV_TAC(DEPTH_CONV
   (NUM_RED_CONV ORELSEC DIMINDEX_CONV ORELSEC INT_RED_CONV)) THEN
  INT_ARITH_TAC;;

let WORD_ARITH tm =
  try
    prove(tm,WORD_ARITH_TAC)
  with Failure m ->
    failwith ("WORD_ARITH `" ^ (string_of_term tm) ^ "`: " ^ m);;

let WORD_ARITH_TAC = CONV_TAC WORD_ARITH;;

(* ------------------------------------------------------------------------- *)
(* Expand a constant into 2 EXP n where possible (e.g. |- 8 = 2 EXP 3)       *)
(* ------------------------------------------------------------------------- *)

let EMPOWER_CONV =
  let rec blog k n =
    if n =/ num_1 then k
    else if n </ num_1 then failwith "Not a power of 2"
    else blog (k + 1) (n // num_2) in
  let exp2 = `(EXP) 2` in
  fun tm ->
    match tm with
      Comb(l,r) when l = exp2 && is_numeral r -> REFL tm
    | _ -> let th = NUM_REDUCE_CONV tm in
           let k = blog 0 (dest_numeral(rand(concl th))) in
           let tm' = mk_comb(exp2,mk_small_numeral k) in
           TRANS th (SYM(NUM_REDUCE_CONV tm'));;

(* ------------------------------------------------------------------------- *)
(* Expand "val x" or "val x DIV 2 EXP k" or "val x MOD 2 EXP k"              *)
(* into a sum over individual bits.                                          *)
(* ------------------------------------------------------------------------- *)

let VAL_EXPAND_CONV =
  let pth_mod = prove
   (`!(x:N word) k.
           val x MOD 2 EXP k =
           if k = 0 then 0
           else nsum (0..k-1) (\i. 2 EXP i * bitval(bit i x))`,
    REPEAT GEN_TAC THEN REWRITE_TAC[VAL_MOD; NUMSEG_LT] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES])
  and pth_div = prove
   (`!(x:N word) k.
           val x DIV 2 EXP k =
           nsum (k..dimindex(:N)-1) (\i. 2 EXP (i - k) * bitval(bit i x))`,
    REPEAT GEN_TAC THEN REWRITE_TAC[VAL_DIV] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
    SIMP_TAC[DIMINDEX_NONZERO; ARITH_RULE
     `~(d = 0) ==> (x <= d - 1 <=> x < d)`]) in
  let base_rule =
   PART_MATCH lhand VAL THENC
   LAND_CONV(RAND_CONV(LAND_CONV(!word_SIZE_CONV) THENC NUM_SUB_CONV))
  and div_rule =
    RAND_CONV EMPOWER_CONV THENC
    PART_MATCH lhand pth_div THENC
    LAND_CONV(RAND_CONV(LAND_CONV(!word_SIZE_CONV) THENC NUM_SUB_CONV))
  and mod_rule =
    RAND_CONV EMPOWER_CONV THENC
    PART_MATCH lhand pth_mod THENC
    RATOR_CONV(LAND_CONV NUM_EQ_CONV) THENC
    GEN_REWRITE_CONV I [COND_CLAUSES] THENC
    TRY_CONV(LAND_CONV(RAND_CONV(NUM_SUB_CONV))) in
  let coreconv tm =
    match tm with
      Comb(Const("val",_),t) -> base_rule tm
    | Comb(Comb(Const("DIV",_),Comb(Const("val",_),_)),n) -> div_rule tm
    | Comb(Comb(Const("MOD",_),Comb(Const("val",_),_)),n) -> mod_rule tm
    | _ -> failwith "VAL_EXPAND_CONV: not of expected form" in
  coreconv THENC
  EXPAND_NSUM_CONV THENC ONCE_DEPTH_CONV NUM_SUB_CONV;;

(* ------------------------------------------------------------------------- *)
(* Zero extension and sign extension (also works for shortening modulo).     *)
(* ------------------------------------------------------------------------- *)

let word_zx = new_definition
 `(word_zx:(M)word->(N)word) w = word(val w)`;;

let VAL_WORD_ZX_GEN = prove
 (`!x. val((word_zx:(M)word->(N)word) x) = val x MOD 2 EXP dimindex(:N)`,
  GEN_TAC THEN REWRITE_TAC[word_zx; VAL_WORD]);;

let VAL_WORD_ZX = prove
 (`!x. dimindex(:M) <= dimindex(:N)
       ==> val((word_zx:(M)word->(N)word) x) = val x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ZX_GEN] THEN
  MATCH_MP_TAC MOD_LT THEN
  TRANS_TAC LTE_TRANS `2 EXP dimindex(:M)` THEN
  ASM_REWRITE_TAC[LE_EXP; VAL_BOUND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let WORD_ZX_ZX = prove
 (`!x. dimindex(:M) <= dimindex(:N)
       ==> (word_zx:N word->M word) ((word_zx:M word->N word) x) = x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `m <= n ==> MIN n m = m`] THEN
  REWRITE_TAC[VAL_MOD_REFL]);;

let WORD_ZX_0 = prove
 (`(word_zx:M word->N word) (word 0) = word 0`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_0; MOD_0]);;

let WORD_ZX_TRIVIAL = prove
 (`!x:N word. word_zx x = x`,
  SIMP_TAC[GSYM VAL_EQ; VAL_WORD_ZX; LE_REFL]);;

let WORD_ZX_WORD = prove
 (`!n. (word_zx:M word->N word) (word n) = word (n MOD 2 EXP dimindex(:M))`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_ZX_GEN]);;

let WORD_ZX_WORD_SIMPLE = prove
 (`!n. dimindex(:N) <= dimindex(:M)
       ==> word_zx(word n:M word):N word = word n`,
  SIMP_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_ZX_GEN] THEN
  SIMP_TAC[MOD_MOD_EXP_MIN; ARITH_RULE `n <= m ==> MIN m n = n`]);;

let WORD_ZX_1 = prove
 (`(word_zx:M word->N word) (word 1) = word 1`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_1; MOD_EQ_SELF] THEN
  DISJ2_TAC THEN REWRITE_TAC[ARITH_RULE `1 < n <=> 2 EXP 1 <= n`] THEN
  REWRITE_TAC[LE_EXP; DIMINDEX_GE_1; DIMINDEX_NONZERO] THEN ARITH_TAC);;

let WORD_ZX_BITVAL = prove
 (`!b. (word_zx:M word->N word) (word(bitval b)) = word(bitval b)`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES; WORD_ZX_0; WORD_ZX_1]);;

let BIT_WORD_ZX = prove
 (`!x i. bit i ((word_zx:M word->N word) x) <=>
         i < dimindex(:N) /\ bit i x`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `i < dimindex(:N)` THENL
   [ASM_REWRITE_TAC[BIT_VAL; VAL_WORD_ZX_GEN];
    ASM_MESON_TAC[BIT_TRIVIAL; NOT_LE]] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `d:num` SUBST1_TAC o REWRITE_RULE[LT_EXISTS]) THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_MOD; ODD_MOD_POW2; NOT_SUC]);;

let WORD_ZX_AND = prove
 (`!(x:M word) (y:M word).
        word_zx(word_and x y):N word =
        word_and (word_zx x) (word_zx y)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ZX; BIT_WORD_AND] THEN
  ONCE_REWRITE_TAC[BIT_GUARD] THEN CONV_TAC TAUT);;

let WORD_ZX_OR = prove
 (`!(x:M word) (y:M word).
        word_zx(word_or x y):N word =
        word_or (word_zx x) (word_zx y)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ZX; BIT_WORD_OR] THEN
  ONCE_REWRITE_TAC[BIT_GUARD] THEN CONV_TAC TAUT);;

let WORD_ZX_XOR = prove
 (`!(x:M word) (y:M word).
        word_zx(word_xor x y):N word =
        word_xor (word_zx x) (word_zx y)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ZX; BIT_WORD_XOR] THEN
  ONCE_REWRITE_TAC[BIT_GUARD] THEN CONV_TAC TAUT);;

let WORD_ZX_NOT = prove
 (`!x:M word.
        dimindex(:N) <= dimindex(:M)
        ==> word_zx(word_not x):N word = word_not(word_zx x)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ZX; BIT_WORD_NOT] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `bit i (x:M word)` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let WORD_ZX_ADD = prove
 (`!(x:M word) (y:M word).
        dimindex(:N) <= dimindex(:M)
        ==> word_zx(word_add x y):N word =
            word_add (word_zx x) (word_zx y)`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; MOD_MOD_EXP_MIN] THEN
  SIMP_TAC[ARITH_RULE `n <= m ==> MIN m n = n`] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]);;

let WORD_ZX_MUL = prove
 (`!(x:M word) (y:M word).
        dimindex(:N) <= dimindex(:M)
        ==> word_zx(word_mul x y):N word =
            word_mul (word_zx x) (word_zx y)`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_MUL; MOD_MOD_EXP_MIN] THEN
  SIMP_TAC[ARITH_RULE `n <= m ==> MIN m n = n`] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]);;

let WORD_ZX_NEG = prove
 (`!x:M word.
        dimindex(:N) <= dimindex(:M)
        ==> word_zx(word_neg x):N word = word_neg(word_zx x)`,
  SIMP_TAC[WORD_NEG_AS_ADD; WORD_ZX_ADD; WORD_ZX_NOT; WORD_ZX_1]);;

let WORD_ZX_SUB = prove
 (`!(x:M word) (y:M word).
        dimindex(:N) <= dimindex(:M)
        ==> word_zx(word_sub x y):N word =
            word_sub (word_zx x) (word_zx y)`,
  REWRITE_TAC[WORD_RULE `word_sub x y = word_add x (word_neg y)`] THEN
  SIMP_TAC[WORD_ZX_NEG; WORD_ZX_ADD]);;

let WORD_ZX_SHL = prove
 (`!(x:M word) n.
        dimindex(:N) <= dimindex(:M)
        ==> word_zx(word_shl x n):N word =
            word_shl (word_zx x) n`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_SHL; MOD_MOD_EXP_MIN] THEN
  SIMP_TAC[ARITH_RULE `n <= m ==> MIN m n = n`] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]);;

let word_sx = new_definition
 `(word_sx:(M)word->(N)word) w = iword(ival w)`;;

let IVAL_WORD_SX = prove
 (`!x. dimindex(:M) <= dimindex(:N)
       ==> ival((word_sx:(M)word->(N)word) x) = ival x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IVAL_IWORD; word_sx] THEN
  MATCH_MP_TAC IVAL_IWORD THEN
  MP_TAC(ISPEC `x:M word` IVAL_BOUND) THEN
  MATCH_MP_TAC(INT_ARITH
   `m:int <= n ==> --m <= x /\ x < m ==> --n <= x /\ x < n`) THEN
  MATCH_MP_TAC INT_POW_MONO THEN CONV_TAC INT_REDUCE_CONV THEN
  ASM_ARITH_TAC);;

let WORD_SX_SX = prove
 (`!x. dimindex(:M) <= dimindex(:N)
       ==> (word_sx:N word->M word) ((word_sx:M word->N word) x) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IVAL_EQ] THEN
  ONCE_REWRITE_TAC[word_sx] THEN ASM_SIMP_TAC[IVAL_WORD_SX; IWORD_IVAL]);;

let WORD_SX_0 = prove
 (`(word_sx:M word->N word) (word 0) = word 0`,
  REWRITE_TAC[GSYM IVAL_EQ; word_sx; IVAL_WORD_0; GSYM WORD_IWORD]);;

let WORD_SX_TRIVIAL = prove
 (`!x:N word. word_sx x = x`,
  SIMP_TAC[GSYM IVAL_EQ; IVAL_WORD_SX; LE_REFL]);;

let WORD_SX_ZX = prove
 (`!x. dimindex(:N) <= dimindex(:M)
       ==> (word_sx:M word->N word) x = word_zx x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[word_sx; word_zx; WORD_IWORD; IWORD_EQ; IVAL_VAL] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(p:int) divides q ==> (x - q * b == x) (mod p)`) THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[INT_POW_ADD] THEN CONV_TAC INTEGER_RULE);;

(* ------------------------------------------------------------------------- *)
(* Sign-extension from a specific bit position in a given word size.         *)
(* ------------------------------------------------------------------------- *)

let word_sxfrom = define
 `word_sxfrom n (x:N word) =
  word_ishr (word_shl x (dimindex(:N) - 1 - n)) (dimindex(:N) - 1 - n)`;;

let BIT_WORD_SXFROM = prove
 (`!n i (x:N word).
        bit i (word_sxfrom n x) <=> i < dimindex(:N) /\ bit (MIN n i) x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_sxfrom; BIT_WORD_SHL; BIT_WORD_ISHR] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  EQ_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let IVAL_WORD_SXFROM_UNIQUE = prove
 (`!(w:N word) k x.
        k < dimindex(:N)
        ==> (ival(word_sxfrom k w) = x <=>
             --(&2 pow k) <= x /\ x < &2 pow k /\
             (ival w == x) (mod (&2 pow (k + 1))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[word_sxfrom; IVAL_WORD_ISHR_SHL_UNIQUE] THEN
  REWRITE_TAC[IVAL_IWORD_GALOIS] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[INT_MUL_SYM] WORD_SHL_AS_IWORD] THEN
  REWRITE_TAC[IWORD_EQ] THEN
  SUBGOAL_THEN
   `(&2:int) pow (dimindex(:N) - 1) =
    &2 pow (dimindex(:N) - 1 - k) * &2 pow k /\
   (&2:int) pow dimindex(:N) =
    &2 pow (dimindex(:N) - 1 - k) * &2 pow (k + 1)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[GSYM INT_POW_ADD] THEN CONJ_TAC THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    SIMP_TAC[GSYM INT_MUL_RNEG; INT_LE_LMUL_EQ; INT_LT_LMUL_EQ; INT_LT_POW2;
             INT_LT_IMP_NE; INTEGER_RULE
              `(a * x:int == a * y) (mod (a * b)) <=>
               a = &0 \/ (x == y) (mod b)`]]);;

(* ------------------------------------------------------------------------- *)
(* Conditional AND and OR, with semantics of C's "&&" and "||"               *)
(* ------------------------------------------------------------------------- *)

let word_cand = new_definition
 `(word_cand:N word->N word->N word) x y =
        if ~(x = word 0) /\ ~(y = word 0) then word 1 else word 0`;;

let word_cor = new_definition
 `(word_cor:N word->N word->N word) x y =
        if ~(x = word 0) \/ ~(y = word 0) then word 1 else word 0`;;

let WORD_CAND = prove
 (`!x y:N word.
        word_cand x y = if x = word 0 \/ y = word 0 then word 0 else word 1`,
  REWRITE_TAC[word_cand] THEN MESON_TAC[]);;

let WORD_COR = prove
 (`!x y:N word.
        word_cor x y = if x = word 0 /\ y = word 0 then word 0 else word 1`,
  REWRITE_TAC[word_cor] THEN MESON_TAC[]);;

let WORD_CAND_NE_0 = prove
 (`!x y:N word.
        ~(word_cand x y = word 0) <=> ~(x = word 0) /\ ~(y = word 0)`,
  REWRITE_TAC[word_cand] THEN MESON_TAC[WORD_NE_10]);;

let WORD_COR_NE_0 = prove
 (`!x y:N word.
        ~(word_cor x y = word 0) <=> ~(x = word 0) \/ ~(y = word 0)`,
  REWRITE_TAC[word_cor] THEN MESON_TAC[WORD_NE_10]);;

let WORD_CAND_EQ_0 = prove
 (`!x y:N word.
        word_cand x y = word 0 <=> x = word 0 \/ y = word 0`,
  REWRITE_TAC[word_cand] THEN MESON_TAC[WORD_NE_10]);;

let WORD_COR_EQ_0 = prove
 (`!x y:N word.
        word_cor x y = word 0 <=> x = word 0 /\ y = word 0`,
  REWRITE_TAC[word_cor] THEN MESON_TAC[WORD_NE_10]);;

let VAL_WORD_CAND = prove
 (`!x y:N word.
        val(word_cand x y) =
        if ~(val x = 0) /\ ~(val y = 0) then 1 else 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_cand; VAL_EQ_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[VAL_WORD_0; VAL_WORD_1]);;

let VAL_WORD_COR = prove
 (`!x y:N word.
        val(word_cor x y) =
        if ~(val x = 0) \/ ~(val y = 0) then 1 else 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_cor; VAL_EQ_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[VAL_WORD_0; VAL_WORD_1]);;

let BIT_WORD_CAND = prove
 (`!i x y:N word.
        bit i (word_cand x y) <=> i = 0 /\ ~(x = word 0) /\ ~(y = word 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_cand] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BIT_WORD_0; BIT_WORD_1]);;

let BIT_WORD_COR = prove
 (`!i x y:N word.
        bit i (word_cor x y) <=> i = 0 /\ (~(x = word 0) \/ ~(y = word 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_cor] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BIT_WORD_0; BIT_WORD_1]);;

(* ------------------------------------------------------------------------- *)
(* Joining, in a somewhat (over?) general sense; v is the high part, w low.  *)
(* ------------------------------------------------------------------------- *)

let word_join = new_definition
 `(word_join:(M)word->(N)word->(P)word) v w =
        word(2 EXP dimindex(:N) * val v + val w)`;;

let VAL_WORD_JOIN = prove
 (`!v w. val((word_join:(M)word->(N)word->(P)word) v w) =
         (2 EXP dimindex(:N) * val v + val w) MOD 2 EXP dimindex(:P)`,
  REWRITE_TAC[word_join; VAL_WORD]);;

let BIT_WORD_JOIN_GEN = prove
 (`!e h l i.
        l < 2 EXP e
        ==> (ODD ((2 EXP e * h + l) DIV 2 EXP i) <=>
             if i < e then ODD(l DIV 2 EXP i) else ODD(h DIV 2 EXP (i - e)))`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LT_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
    REWRITE_TAC[EXP_ADD; EXP; GSYM MULT_ASSOC] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ODD_MULT; ODD_ADD; ARITH];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LT]) THEN
    DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ; EXP_ADD; GSYM DIV_DIV] THEN
    ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES; ADD_SUB2]]);;

let BIT_WORD_JOIN = prove
 (`!v w i.
        bit i ((word_join:(M)word->(N)word->(P)word) v w) <=>
        i < dimindex(:P) /\
        (if i < dimindex(:N) then bit i w else bit (i - dimindex(:N)) v)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `i < dimindex(:P)` THEN
  ASM_SIMP_TAC[BIT_TRIVIAL; GSYM NOT_LT] THEN
  REWRITE_TAC[word_join; BIT_WORD] THEN ASM_REWRITE_TAC[BIT_VAL] THEN
  SIMP_TAC[BIT_WORD_JOIN_GEN; VAL_BOUND]);;

let VAL_WORD_JOIN_SIMPLE = prove
 (`!v w.
        dimindex(:M) + dimindex(:N) = dimindex(:P)
        ==> val((word_join:(M)word->(N)word->(P)word) v w) =
            2 EXP dimindex(:N) * val v + val w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_JOIN] THEN
  MATCH_MP_TAC MOD_LT THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  TRANS_TAC LTE_TRANS
   `2 EXP dimindex(:N) * (2 EXP dimindex(:M) - 1) + 2 EXP dimindex(:N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LET_ADD2 THEN REWRITE_TAC[VAL_BOUND; LE_MULT_LCANCEL] THEN
    DISJ2_TAC THEN MATCH_MP_TAC(ARITH_RULE `a < b ==> a <= b - 1`) THEN
    REWRITE_TAC[VAL_BOUND];
    REWRITE_TAC[LEFT_SUB_DISTRIB; EXP_ADD] THEN MATCH_MP_TAC(ARITH_RULE
     `n * 1 <= n * m ==> n * m - n * 1 + n <= m * n`) THEN
    REWRITE_TAC[LE_MULT_LCANCEL; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ]]);;

let WORD_JOIN_NOT = prove
 (`!v w. dimindex(:P) <= dimindex(:M) + dimindex(:N)
         ==> (word_join:(M)word->(N)word->(P)word) (word_not v) (word_not w) =
             word_not(word_join v w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  SIMP_TAC[BIT_WORD_JOIN; BIT_WORD_NOT; COND_SWAP] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[BIT_GUARD] THEN EQ_TAC THEN SIMP_TAC[] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Subwords, where the (pos,len) argument is (lsb_position,length)           *)
(* ------------------------------------------------------------------------- *)

let word_subword = new_definition
 `word_subword (w:M word) (pos,len):N word =
        word((val w DIV (2 EXP pos)) MOD (2 EXP len))`;;

let VAL_WORD_SUBWORD = prove
 (`!pos len w:M word.
        val(word_subword w (pos,len):N word) =
        (val w DIV (2 EXP pos)) MOD (2 EXP (MIN len (dimindex(:N))))`,
  REWRITE_TAC[word_subword; VAL_WORD; MOD_MOD_EXP_MIN]);;

let VAL_WORD_SUBWORD_DIMINDEX = prove
 (`!pos w:M word.
        val(word_subword w (pos,dimindex(:N)):N word) =
        (val w DIV (2 EXP pos)) MOD (2 EXP dimindex(:N))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUBWORD] THEN
  REWRITE_TAC[ARITH_RULE `MIN n n = n`]);;

let VAL_WORD_SUBWORD_SIMPLE = prove
 (`!w:M word.
        val(word_subword w (0,dimindex(:N)):N word) =
        val w MOD (2 EXP dimindex(:N))`,
  REWRITE_TAC[VAL_WORD_SUBWORD_DIMINDEX; EXP; DIV_1]);;

let WORD_SUBWORD_WORD = prove
 (`!n pos len.
        pos + len <= dimindex(:N)
        ==> word_subword (word n:N word) (pos,len) =
            word((n DIV 2 EXP pos) MOD 2 EXP len)`,
  REPEAT STRIP_TAC THEN SIMP_TAC[word_subword; DIV_MOD; GSYM EXP_ADD] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[VAL_WORD; MOD_MOD_EXP_MIN] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let BIT_WORD_SUBWORD = prove
 (`!pos len (w:M word) i.
        bit i (word_subword w (pos,len):N word) <=>
        i < MIN len (dimindex(:N)) /\ bit (pos + i) w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `m < MIN p q <=> m < p /\ m < q`] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN
  ASM_SIMP_TAC[GSYM NOT_LT; BIT_TRIVIAL] THEN
  ASM_REWRITE_TAC[word_subword; BIT_WORD] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; BIT_VAL; DIV_DIV] THEN
  ASM_CASES_TAC `i:num < len` THEN ASM_REWRITE_TAC[] THENL
   [UNDISCH_TAC `i:num < len` THEN
    SIMP_TAC[LT_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d:num` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ADD_ASSOC] THEN
    SPEC_TAC(`pos + i:num`,`j:num`) THEN REWRITE_TAC[EXP_ADD] THEN
    REWRITE_TAC[GSYM DIV_MOD; ODD_MOD_POW2; NOT_SUC];
    MATCH_MP_TAC(MESON[ODD] `n = 0 ==> ~ODD n`) THEN
    SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LTE_TRANS `2 EXP (pos + len)` THEN
    SIMP_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ; LE_EXP] THEN
    ASM_ARITH_TAC]);;

let WORD_SUBWORD_0 = prove
 (`!pos len. word_subword (word 0) (pos,len) = word 0`,
  REWRITE_TAC[word_subword; VAL_WORD_0; DIV_0; MOD_0]);;

let WORD_SUBWORD_JOIN_SELF = prove
 (`!(w:N word) k.
        k <= dimindex(:N)
        ==> word_subword (word_join w w:(N tybit0)word) (k,dimindex(:N)) =
            word_ror w k`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_ROR;
              DIMINDEX_TYBIT0; ARITH_RULE `MIN n n = n`] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC o MATCH_MP (ARITH_RULE
   `k:num <= n ==> k = n \/ k < n`)) THEN
  ASM_SIMP_TAC[MOD_REFL; MOD_LT; ADD_CLAUSES;
               ARITH_RULE `(n + i) - n:num = i`;
               ARITH_RULE `~(n + i:num < n)`;
               ARITH_RULE `i < n ==> n + i < 2 * n`] THEN
  REWRITE_TAC[ADD_SYM; TAUT `(p /\ q <=> q) <=> q ==> p`] THEN
  DISCH_THEN(K ALL_TAC) THEN ASM_ARITH_TAC);;

let VAL_WORD_SUBWORD_JOIN = prove
 (`!(h:N word) (l:N word) n m.
        m <= dimindex(:N)
        ==> val(word_subword (word_join h l:(N tybit0)word) (n,m) :N word) =
            ((2 EXP dimindex(:N) * val h + val l) DIV 2 EXP n) MOD 2 EXP m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_JOIN; VAL_WORD_SUBWORD] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN; DIMINDEX_TYBIT0] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC(MESON[MOD_LT]
   `!e. x < e /\ x MOD e MOD m = x MOD e MOD n ==> x MOD m = x MOD n`) THEN
  EXISTS_TAC `2 EXP (2 * dimindex(:N))` THEN CONJ_TAC THENL
   [REWRITE_TAC[MULT_2; EXP_ADD] THEN MATCH_MP_TAC (ARITH_RULE
     `e * h + e * 1 <= e * e /\ l < e ==> e * h + l < e * e`) THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; LE_MULT_LCANCEL; VAL_BOUND;
                EXP_EQ_0; ARITH_EQ; ARITH_RULE `h + 1 <= e <=> h < e`];
    REWRITE_TAC[MOD_MOD_EXP_MIN] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC]);;

let WORD_SUBWORD_JOIN_LOWER = prove
 (`!(h:M word) (l:N word) pos len.
        pos + len <= dimindex(:N) /\ dimindex(:N) <= dimindex(:P)
        ==> word_subword (word_join (h:M word) (l:N word):P word)
                         (pos,len):Q word =
            word_subword l (pos,len)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_JOIN] THEN
  REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY ASM_ARITH_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let WORD_SUBWORD_JOIN_UPPER = prove
 (`!(h:M word) (l:N word) pos len.
        dimindex(:N) <= pos /\ pos + len <= dimindex(:P)
        ==> word_subword (word_join (h:M word) (l:N word):P word)
                         (pos,len):Q word =
            word_subword h (pos - dimindex(:N),len)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_JOIN] THEN
  REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY ASM_ARITH_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  BINOP_TAC THEN TRY(AP_THM_TAC THEN AP_TERM_TAC) THEN ASM_ARITH_TAC);;

let WORD_SUBWORD_SUBWORD = prove
 (`!(x:M word) pos1 len1 pos2 len2.
        len1 <= dimindex(:N) /\ dimindex(:N) <= dimindex(:M)
        ==> word_subword (word_subword x (pos1,len1):N word)
                         (pos2,len2):P word =
            word_subword x (pos1+pos2,MIN len2 (len1-pos2))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BIT_GUARD]) THEN
  ASM_ARITH_TAC);;

let WORD_SUBWORD_TRIVIAL = prove
 (`!(x:N word) n. dimindex(:N) <= n ==> word_subword x (0,n) = x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; ADD_CLAUSES] THEN
  ASM_SIMP_TAC[ARITH_RULE `N:num <= n ==> MIN n N = N`]);;

let WORD_SUBWORD_DIMINDEX = prove
 (`!(x:N word) k.
        word_subword x (k,dimindex(:M)):M word = word_zx(word_ushr x k)`,
  REWRITE_TAC[word_subword; word_zx; VAL_WORD_USHR; WORD_MOD_SIZE]);;

let WORD_ZX_SUBWORD = prove
 (`!(x:N word). word_zx x:M word = word_subword x (0,dimindex(:M))`,
  REWRITE_TAC[WORD_SUBWORD_DIMINDEX; WORD_USHR_ZERO]);;

let VAL_WORD_SUBWORD_JOIN_FULL = prove
 (`!(h:N word) (l:N word) k.
       k <= dimindex(:N)
       ==> val(word_subword (word_join h l:(N tybit0)word)
                            (k,dimindex(:N)) :N word) =
           2 EXP (dimindex(:N) - k) * val h MOD 2 EXP k + val l DIV (2 EXP k)`,
  REPEAT STRIP_TAC THEN SIMP_TAC[VAL_WORD_SUBWORD_JOIN; LE_REFL] THEN
  MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `val(h:N word) DIV 2 EXP k` THEN
  SUBGOAL_THEN `2 EXP dimindex(:N) = 2 EXP k * 2 EXP (dimindex(:N) - k)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    SIMP_TAC[GSYM MULT_ASSOC; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ]] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[DIVISION_SIMP; ARITH_RULE
     `d * k * e + e * m + l:num = e * (d * k + m) + l`];
    MATCH_MP_TAC(ARITH_RULE
     `d < e /\ e * (m + 1) <= e * k ==> e * m + d < k * e`) THEN
    REWRITE_TAC[LE_MULT_LCANCEL; ARITH_RULE `a + 1 <= b <=> a < b`] THEN
    SIMP_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ; RDIV_LT_EQ] THEN
    ASM_SIMP_TAC[GSYM EXP_ADD; ARITH_RULE `k:num <= d ==> k + d - k = d`] THEN
    REWRITE_TAC[VAL_BOUND]]);;

let WORD_SUBWORD_JOIN_AS_USHR = prove
 (`!(x:N word) k.
      word_subword (word_join (word 0:N word) x:((N)tybit0)word)
                   (k,dimindex(:N)) =
      word_ushr x k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  SIMP_TAC[VAL_WORD_USHR; VAL_WORD_SUBWORD_JOIN; LE_REFL] THEN
  REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
  MATCH_MP_TAC MOD_LT THEN MESON_TAC[DIV_LE; VAL_BOUND; LET_TRANS]);;

let WORD_SUBWORD_JOIN_AS_SHL = prove
 (`!(x:N word) k.
        k <= dimindex(:N)
        ==> word_subword (word_join x (word 0:N word):((N)tybit0)word)
                         (k,dimindex(:N)) =
            word_shl x (dimindex(:N) - k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  SIMP_TAC[VAL_WORD_SHL; VAL_WORD_SUBWORD_JOIN; LE_REFL] THEN
  REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `2 EXP dimindex(:N) = 2 EXP k * 2 EXP (dimindex(:N) - k)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    SIMP_TAC[GSYM MULT_ASSOC; DIV_MULT; EXP_EQ_0; ARITH_EQ]]);;

let WORD_SUBWORD_AS_USHR = prove
 (`!(x:N word) k l.
        dimindex(:N) <= k + l ==> word_subword x (k,l) = word_ushr x k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_subword; word_ushr] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN
  SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
  W(MP_TAC o PART_MATCH lhand VAL_BOUND o lhand o snd) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LTE_TRANS) THEN
  ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC);;

let WORD_USHR_AS_SUBWORD = prove
 (`!(x:N word) k. word_ushr x k = word_subword x (k,dimindex (:N) - k)`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC WORD_SUBWORD_AS_USHR THEN ARITH_TAC);;

let WORD_SHL_SUBWORD = prove
 (`!(x:N word) d l.
        dimindex(:N) <= l + d
        ==> word_shl (word_subword x (0,l)) d = word_shl x d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_shl; word_subword] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; EXP; DIV_1] THEN
  CONV_TAC MOD_DOWN_CONV THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  REWRITE_TAC[GSYM MOD_MULT2; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= l + d ==> MIN (d + l) n = n`]);;

let WORD_SUBWORD_AND = prove
 (`!(x:M word) y pos len.
        word_subword (word_and x y) (pos,len) :N word =
        word_and (word_subword x (pos,len)) (word_subword y (pos,len))`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_AND] THEN
  ONCE_REWRITE_TAC[BIT_GUARD] THEN CONV_TAC TAUT);;

let WORD_SUBWORD_OR = prove
 (`!(x:M word) y pos len.
        word_subword (word_or x y) (pos,len) :N word =
        word_or (word_subword x (pos,len)) (word_subword y (pos,len))`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_OR] THEN
  ONCE_REWRITE_TAC[BIT_GUARD] THEN CONV_TAC TAUT);;

let WORD_SUBWORD_XOR = prove
 (`!(x:M word) y pos len.
        word_subword (word_xor x y) (pos,len) :N word =
        word_xor (word_subword x (pos,len))
                 (word_subword y (pos,len))`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_XOR] THEN
  ONCE_REWRITE_TAC[BIT_GUARD] THEN CONV_TAC TAUT);;

let WORD_SUBWORD_NOT = prove
 (`!(x:M word) pos len.
        dimindex(:N) <= len /\ pos + len <= dimindex(:M)
        ==> word_subword (word_not x) (pos,len):N word =
            word_not (word_subword x (pos,len))`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_NOT] THEN
  SIMP_TAC[ARITH_RULE `i < MIN m n <=> i < m /\ i < n`] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[DE_MORGAN_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let WORD_SUBWORD_ADD = prove
 (`!x y:N word.
        dimindex(:M) = len /\ pos + len <= dimindex(:N) /\
        val x MOD 2 EXP pos + val y MOD 2 EXP pos < 2 EXP pos
        ==> word_subword (word_add x y) (pos,len):M word =
            word_add (word_subword x (pos,len))
                     (word_subword y (pos,len))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD_SUBWORD] THEN
  FIRST_ASSUM SUBST1_TAC THEN REWRITE_TAC[ARITH_RULE `MIN n n = n`] THEN
  CONV_TAC MOD_DOWN_CONV THEN ASM_SIMP_TAC[GSYM DIV_ADD_EQ] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `m <= n ==> MIN n m = m`]);;

let WORD_SUBWORD_AS_IWORD = prove
 (`!(w:N word) pos len.
        pos + len <= dimindex(:N)
        ==> word_subword w (pos,len):M word =
            iword((ival w div &2 pow pos) rem &2 pow len)`,
  REPEAT STRIP_TAC THEN SIMP_TAC[INT_DIV_REM; INT_POW_LE; INT_POS] THEN
  ASM_SIMP_TAC[GSYM INT_POW_ADD; INT_REM_IVAL] THEN
  REWRITE_TAC[word_subword; INT_OF_NUM_DIV; INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[WORD_IWORD; EXP_ADD; GSYM DIV_MOD]);;

let WORD_SUBWORD_IWORD = prove
 (`!x pos len.
        pos + len <= dimindex(:N)
        ==> word_subword (iword x:N word) (pos,len):M word =
            iword((x div &2 pow pos) rem &2 pow len)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WORD_SUBWORD_AS_IWORD] THEN
  SIMP_TAC[INT_DIV_REM; INT_POW_LE; INT_POS; GSYM INT_POW_ADD] THEN
  ASM_SIMP_TAC[INT_REM_IVAL_IWORD]);;

let WORD_SUBWORD_IWORD = prove
 (`!x pos len.
        pos + len <= dimindex(:N)
        ==> word_subword (iword x:N word) (pos,len):N word =
            iword((x div &2 pow pos) rem &2 pow len)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WORD_SUBWORD_AS_IWORD] THEN
  SIMP_TAC[INT_DIV_REM; INT_POW_LE; INT_POS; GSYM INT_POW_ADD] THEN
  ASM_SIMP_TAC[INT_REM_IVAL_IWORD]);;

let WORD_SUBWORD_AS_USHR_SHL = prove (`!(x:N word) pos len.
        pos + len <= dimindex(:N)
        ==> word_subword x (pos,len):N word =
            word_ushr (word_shl x (dimindex(:N) - (pos + len)))
                      (dimindex(:N) - len)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD;
              BIT_WORD_USHR; BIT_WORD_SHL] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[BIT_GUARD] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN MATCH_MP_TAC(TAUT
   `(p <=> p') /\ (p /\ p' ==> (q <=> q')) ==> (p /\ q <=> p' /\ q')`) THEN
  CONJ_TAC THENL [ALL_TAC; STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC] THEN
  ASM_ARITH_TAC);;

let WORD_SXFROM_SUBWORD_AS_ISHR_SHL = prove
 (`!(x:N word) pos len.
        pos + len <= dimindex(:N) /\ 0 < len
        ==> word_sxfrom (len-1) (word_subword x (pos,len)):N word =
            word_ishr (word_shl x (dimindex(:N) - (pos + len)))
                      (dimindex(:N) - len)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_SXFROM;
              BIT_WORD_ISHR; BIT_WORD_SHL] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ONCE_REWRITE_TAC[BIT_GUARD] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN MATCH_MP_TAC(TAUT
   `(p <=> p') /\ (p /\ p' ==> (q <=> q')) ==> (p /\ q <=> p' /\ q')`) THEN
  (CONJ_TAC THENL [ALL_TAC; STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC]) THEN
  ASM_ARITH_TAC);;

let VAL_EXPAND_SUBWORDS = prove
 (`!k m (x:N word).
        dimindex(:M) = k /\ dimindex(:N) = k * m
        ==> nsum {i | i < m}
                 (\i.  2 EXP (k * i) *
                       val(word_subword x (k * i,k):M word)) =
            val x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[val_def; GSYM NSUM_LMUL; BIT_WORD_SUBWORD] THEN
  POP_ASSUM_LIST(CONV_TAC o SUBS_CONV) THEN
  REWRITE_TAC[MULT_ASSOC; GSYM EXP_ADD; ARITH_RULE `MIN n n = n`] THEN
  SIMP_TAC[NSUM_NSUM_PRODUCT; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC NSUM_EQ_GENERAL_INVERSES THEN
  MAP_EVERY EXISTS_TAC [`\(i,j). (k:num) * i + j`; `\n. n DIV k,n MOD k`] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM; PAIR_EQ] THEN SIMP_TAC[IN_ELIM_THM] THEN
  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[LT; MULT_CLAUSES] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; DIVISION_SIMP; MOD_MULT_ADD; DIV_LT; MOD_LT] THEN
  ASM_SIMP_TAC[MOD_LT_EQ; RDIV_LT_EQ; ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN TRANS_TAC LTE_TRANS `k * i + k:num` THEN
  ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN
  ASM_REWRITE_TAC[ARITH_RULE `k * i + k = k * (i + 1)`] THEN
  REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

let VAL_SUBWORDS_EQ = prove
 (`!k m f (x:N word).
        dimindex(:M) = k /\ dimindex(:N) = k * m
        ==> ((!i. i < m ==> val(word_subword x (k * i,k):M word) = f i) <=>
             (!i. i < m ==> f i < 2 EXP k) /\
             val x = nsum {i | i < m} (\i.  2 EXP (k * i) * f i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. i < m ==> val(word_subword (x:N word) (k * i,k):M word) < 2 EXP k`
  ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN REWRITE_TAC[VAL_BOUND];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(p ==> q) /\ (q ==> (p <=> r)) ==> (p <=> q /\ r)`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`k:num`; `m:num`; `x:N word`] VAL_EXPAND_SUBWORDS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ASM_SIMP_TAC[DIGITSUM_UNIQUE; EXP_MULT; IN_ELIM_THM; FINITE_NUMSEG_LT] THEN
  MESON_TAC[]);;

let WORD_SUBWORDS_EQ = prove
 (`!k m f (x:N word).
        dimindex(:M) = k /\ dimindex(:N) = k * m
        ==> ((!i. i < m ==> val(word_subword x (k * i,k):M word) = f i) <=>
             (!i. i < m ==> f i < 2 EXP k) /\
             word(nsum {i | i < m} (\i.  2 EXP (k * i) * f i)) = x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP VAL_SUBWORDS_EQ th]) THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)`) THEN
  DISCH_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  FIRST_X_ASSUM(SUBST1_TAC o CONJUNCT2) THEN
  ASM_SIMP_TAC[EXP_MULT; DIGITSUM_BOUND; IN_ELIM_THM; FINITE_NUMSEG_LT]);;

(* ------------------------------------------------------------------------- *)
(* Extract bottom len bits of x' and insert into x at position pos.          *)
(* ------------------------------------------------------------------------- *)

let word_insert = new_definition
 `(word_insert:N word->num#num->M word->P word) x (pos,len) x' =
        word(2 EXP (pos + len) * val x DIV 2 EXP (pos + len) +
             2 EXP pos * val x' MOD 2 EXP len +
             val x MOD 2 EXP pos)`;;

let BIT_WORD_INSERT = prove
 (`!(x:N word) (x':M word) pos len i.
        bit i (word_insert x (pos,len) x':P word) <=>
        i < dimindex(:P) /\
        (if pos <= i /\ i < pos + len then bit (i - pos) x' else bit i x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_insert; BIT_WORD] THEN
  ASM_CASES_TAC `i < dimindex(:P)` THEN ASM_REWRITE_TAC[BIT_VAL] THEN
  REWRITE_TAC[EXP_ADD; ARITH_RULE
   `(p * q) * h + p * m + l:num = p * (q * h + m) + l`] THEN
  SIMP_TAC[BIT_WORD_JOIN_GEN; MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
  ASM_CASES_TAC `i:num < pos` THEN ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `~(i:num < pos) ==> (i - pos < len <=> i < pos + len)`] THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_SIMP_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE
   `~(i:num < pos + len) ==> (pos + len) + i - pos - len = i`] THEN
  REWRITE_TAC[ODD_MOD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC CONG_DIV2 THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] (GSYM(CONJUNCT2 EXP))] THEN
  REWRITE_TAC[CONG; MOD_MOD_EXP_MIN] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let WORD_SUBWORD_INSERT_OUTER = prove
 (`!(x:M word) (y:N word) pos1 len1 pos2 len2.
        pos2 + len2 <= dimindex(:P) /\
        (pos2 + len2 <= pos1 \/ pos1 + len1 <= pos2)
        ==> word_subword (word_insert x (pos1,len1) y:P word)
                         (pos2,len2):Q word =
            word_subword x (pos2,len2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_INSERT] THEN
  REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY ASM_ARITH_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BIT_GUARD]) THEN
  ASM_ARITH_TAC);;

let WORD_SUBWORD_INSERT_INNER = prove
 (`!(x:M word) (y:N word) pos1 len1 pos2 len2.
        pos2 + len2 <= dimindex(:P) /\
        pos1 <= pos2 /\ pos2 + len2 <= pos1 + len1
        ==> word_subword (word_insert x (pos1,len1) y:P word)
                         (pos2,len2):Q word =
            word_subword y (pos2-pos1,len2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_INSERT] THEN
  REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY ASM_ARITH_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BIT_GUARD]) THEN
  TRY ASM_ARITH_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Repetition of a shorter word in a longer one. This uses the argument      *)
(* word size type as the only indication of word length for the argument.    *)
(* ------------------------------------------------------------------------- *)

let word_duplicate = new_definition
 `(word_duplicate:M word->N word) x =
  word_of_bits {i | bit (i MOD dimindex(:M)) x}`;;

let BIT_WORD_DUPLICATE = prove
 (`!(x:M word) i.
        bit i (word_duplicate x:N word) <=>
        i < dimindex(:N) /\ bit (i MOD dimindex(:M)) x`,
  REWRITE_TAC[word_duplicate; BIT_WORD_OF_BITS; IN_ELIM_THM]);;

let WORD_DUPLICATE_REFL = prove
 (`!x:N word. word_duplicate x = x`,
  SIMP_TAC[WORD_EQ_BITS_ALT; BIT_WORD_DUPLICATE; MOD_LT]);;

let WORD_DUPLICATE_DOUBLE = prove
 (`!x:M word. (word_duplicate:((M)tybit0)word->N word) (word_join x x) =
              word_duplicate x`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_DUPLICATE] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[BIT_WORD_JOIN; DIMINDEX_TYBIT0] THEN
  MP_TAC(SPECL [`i MOD (2 * dimindex(:M))`; `dimindex(:M)`] MOD_CASES) THEN
  REWRITE_TAC[MOD_LT_EQ; MULT_EQ_0; DIMINDEX_NONZERO; ARITH_EQ] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] MOD_MOD] THEN MESON_TAC[]);;

let WORD_SUBWORD_DUPLICATE = prove
 (`!x pos len.
        pos MOD dimindex(:M) + len <= dimindex(:M) /\
        pos + len <= dimindex(:N)
        ==> word_subword ((word_duplicate:M word->N word) x) (pos,len):P word =
            word_subword x (pos MOD dimindex(:M),len)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_DUPLICATE] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `i < MIN m n <=> i < m /\ i < n`] THEN
  ASM_CASES_TAC `i:num < len` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q <=> r) ==> (p /\ q <=> r)`) THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; AP_THM_TAC THEN AP_TERM_TAC] THEN
  MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `pos DIV dimindex(:M)` THEN
  ASM_ARITH_TAC);;

let WORD_SUBWORD_DUPLICATE_DUPLICATE = prove
 (`!x pos len.
        pos MOD dimindex(:M) = 0 /\ dimindex(:P) <= len /\
        pos + len <= dimindex(:N)
        ==> word_subword ((word_duplicate:M word->N word) x) (pos,len):P word =
            word_duplicate x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_DUPLICATE] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `i < MIN m n <=> i < m /\ i < n`] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN
  MATCH_MP_TAC(TAUT `p /\ (q <=> r) ==> (p /\ q <=> r)`) THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; AP_THM_TAC THEN AP_TERM_TAC] THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; MOD_MOD_REFL]);;

let VAL_WORD_DUPLICATE = prove
 (`!x k. dimindex(:N) <= k * dimindex(:M)
         ==> val((word_duplicate:M word->N word) x) =
             ((2 EXP (k * dimindex(:M)) - 1) DIV (2 EXP dimindex(:M) - 1) *
              val x) MOD 2 EXP dimindex(:N)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM VAL_MOD_REFL] THEN
  MP_TAC(ISPECL
   [`\i. i DIV dimindex(:M)`;
    `\i. 2 EXP i * bitval (bit (i MOD dimindex(:M)) (x:M word))`;
    `{i | i < k * dimindex(:M)}`; `{i:num | i < k}`]
   NSUM_GROUP) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  ANTS_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; DIMINDEX_NONZERO; MULT_AC]; ALL_TAC] THEN
  MATCH_MP_TAC(MESON[MOD_MOD_REFL]
   `y MOD n = y' /\ x = x' ==> x = y ==> y' MOD n = x' MOD n`) THEN
  CONJ_TAC THENL
   [SIMP_TAC[val_def; BINARY_DIGITSUM_MOD; FINITE_NUMSEG_LT] THEN
    SIMP_TAC[BIT_WORD_DUPLICATE; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[ARITH_RULE `a:num <= b ==> (i < b /\ i < a <=> i < a)`];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `nsum {i | i < k} (\i. 2 EXP (dimindex(:M) * i) * val(x:M word))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[val_def; GSYM NSUM_LMUL] THEN
    MATCH_MP_TAC NSUM_EQ_GENERAL_INVERSES THEN
    EXISTS_TAC `\j. j MOD dimindex(:M)` THEN
    EXISTS_TAC `\j:num. dimindex(:M) * i + j` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; DIMINDEX_NONZERO; MOD_LT; DIV_LT;
             MOD_LT_EQ; ADD_CLAUSES] THEN
    CONJ_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THENL
     [TRANS_TAC LTE_TRANS `(i + 1) * dimindex(:M)` THEN
      ASM_REWRITE_TAC[LE_MULT_RCANCEL; DIMINDEX_NONZERO] THEN ASM_ARITH_TAC;
      REWRITE_TAC[MULT_ASSOC; GSYM EXP_ADD] THEN ASM_MESON_TAC[DIVISION_SIMP]];
    REWRITE_TAC[NSUM_RMUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `0 < e - 1 <=> 2 EXP 1 <= e`] THEN
    SIMP_TAC[LE_EXP; LE_1; DIMINDEX_NONZERO; ARITH_EQ] THEN
    CONV_TAC SYM_CONV THEN SPEC_TAC(`k:num`,`k:num`) THEN
    MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT] THEN
    SIMP_TAC[MULT_CLAUSES; EXP; SUB_REFL] THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN
    SIMP_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
    SIMP_TAC[GSYM INT_OF_NUM_SUB; LE_1; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_POW; EXP_ADD] THEN
    REWRITE_TAC[ARITH_RULE `i * dimindex(:M) = dimindex(:M) * i`] THEN
    REWRITE_TAC[INT_POW_ADD] THEN CONV_TAC INT_ARITH]);;

let WORD_DUPLICATE = prove
 (`!m k. dimindex(:N) <= k * dimindex(:M)
         ==> (word_duplicate:M word->N word)(word m) =
             word((2 EXP (k * dimindex(:M)) - 1) DIV
                  (2 EXP dimindex(:M) - 1) * m MOD 2 EXP dimindex(:M))`,
  SIMP_TAC[REWRITE_RULE[VAL_WORD_GALOIS] VAL_WORD_DUPLICATE] THEN
  REWRITE_TAC[VAL_WORD; WORD_MOD_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* Reduce some "simple" subword expressions, those that are simply           *)
(* equivalent to related ones for subexpresions of the word argument.        *)
(* ------------------------------------------------------------------------- *)

let WORD_SUBWORD_ZX = prove
 (`!x pos len.
        MIN (pos + dimindex(:P)) (dimindex(:M)) <= dimindex(:N)
        ==> word_subword ((word_zx:M word->N word) x) (pos,len):P word =
               word_subword x (pos,len)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_ZX] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `i:num < len` THEN
  ASM_REWRITE_TAC[ARITH_RULE `i < MIN a b <=> i < a /\ i < b`] THEN
  ONCE_REWRITE_TAC[BIT_GUARD] THEN
  REWRITE_TAC[TAUT `(p /\ q <=> q) <=> q ==> p`] THEN STRIP_TAC THEN
  ASM_ARITH_TAC);;

let WORD_SUBWORD_ZX_TRIVIAL = prove
 (`!x pos len.
        MIN (dimindex(:M)) (dimindex(:N)) <= pos
        ==> word_subword ((word_zx:M word->N word) x) (pos,len):P word =
            word 0`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_ZX; BIT_WORD_0] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[BIT_GUARD] THEN ASM_ARITH_TAC);;

let WORD_SIMPLE_SUBWORD_CONV =
  let dimarith_conv = DEPTH_CONV(!word_SIZE_CONV ORELSEC NUM_RED_CONV) in
  let dimarith_rule th =
    MP th (EQT_ELIM(dimarith_conv(lhand(concl th))))
  and post_rule =
     CONV_RULE(RAND_CONV(RAND_CONV(BINOP_CONV dimarith_conv)))
  and triv_rule =
     GEN_REWRITE_RULE (RAND_CONV o TRY_CONV) [WORD_DUPLICATE_REFL] in
  let [rules_join; rules_insert; rules_zx; rules_subword; rules_duplicate;
       [rule_duplicate]; [rule_trivial]] =
  map (map (PART_MATCH (lhand o rand)))
   [[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER];
    [WORD_SUBWORD_INSERT_OUTER; WORD_SUBWORD_INSERT_INNER];
    [WORD_SUBWORD_ZX_TRIVIAL; WORD_SUBWORD_ZX];
    [WORD_SUBWORD_SUBWORD]; [WORD_SUBWORD_DUPLICATE];
    [WORD_SUBWORD_DUPLICATE_DUPLICATE];
    [WORD_SUBWORD_TRIVIAL]] in
  fun tm ->
    match tm with
      Comb(Comb(Const("word_subword",_),itm),
           Comb(Comb(Const(",",_),Comb(Const("NUMERAL",_),_)),
                Comb(Const("NUMERAL",_),_))) ->
      (try dimarith_rule(rule_trivial tm) with Failure _ ->
       (match itm with
          Comb(Comb(Const("word_join",_),_),_) ->
             post_rule(tryfind (fun f -> dimarith_rule(f tm)) rules_join)
        | Comb(Comb(Comb(Const("word_insert",_),_),_),_) ->
             post_rule(tryfind (fun f -> dimarith_rule(f tm)) rules_insert)
        | Comb(Comb(Const("word_subword",_),_),_) ->
             post_rule(tryfind (fun f -> dimarith_rule(f tm)) rules_subword)
        | Comb(Const("word_zx",_),_) ->
             tryfind (fun f -> dimarith_rule(f tm)) rules_zx
        | Comb(Const("word_duplicate",_),_) ->
           (try triv_rule(dimarith_rule(rule_duplicate tm))
            with Failure _ ->
             post_rule(tryfind (fun f -> dimarith_rule(f tm)) rules_duplicate))
        | _ -> failwith "WORD_SIMPLE_SUBWORD_CONV"))
    | _ -> failwith "WORD_SIMPLE_SUBWORD_CONV";;

(* ------------------------------------------------------------------------- *)
(* Bit recursion equations for "linear" operations.                          *)
(* ------------------------------------------------------------------------- *)

let BIT_WORD_ADD = prove
 (`!x (y:N word) i.
        bit i (word_add x y) <=>
        i < dimindex(:N) /\
        ((bit i x <=> bit i y) <=>
         ~(i = 0) /\
         (bit (i - 1) x /\ bit (i - 1) y \/
          (bit (i - 1) x \/ bit (i - 1) y) /\
          ~(bit (i - 1) (word_add x y))))`,
  let lemma = prove
   (`2 EXP i <= (2 EXP i * b + x) MOD 2 EXP (i + 1) <=>
     (EVEN b <=> 2 EXP i <= x MOD (2 EXP (i + 1)))`,
    SIMP_TAC[EXP_ADD; EXP_1; MOD_MULT_MOD; EXP_EQ_0; ARITH_EQ;
             DIV_MULT_ADD; MOD_MULT_ADD] THEN
    REWRITE_TAC[MOD_2_CASES; EVEN_ADD] THEN
    MAP_EVERY ASM_CASES_TAC [`EVEN b`; `EVEN(x DIV 2 EXP i)`] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; LE_ADD; NOT_LE] THEN
    SIMP_TAC[DIVISION; EXP_EQ_0; ARITH_EQ]) in
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `i < dimindex(:N)` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[NOT_LT; BIT_TRIVIAL]] THEN
  GEN_REWRITE_TAC LAND_CONV [BIT_VAL_MOD] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [BIT_VAL_MOD] THEN
  ASM_REWRITE_TAC[VAL_WORD_ADD; MOD_MOD_EXP_MIN] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [TAUT `~p /\ q <=> ~(~p ==> ~q)`] THEN
  ASM_SIMP_TAC[SUB_ADD; LE_1; ARITH_RULE
    `~(k = 0) /\ k < n ==> MIN n (k - 1 + 1) = k`] THEN
  ASM_SIMP_TAC[NOT_IMP; ARITH_RULE `k < n ==> MIN n (k + 1) = k + 1`] THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
  REWRITE_TAC[VAL_MOD_STEP; lemma; ARITH_RULE
   `(k * b + x) + (k * c + y):num = k * (b + c) + x + y`] THEN
  BINOP_TAC THENL
   [MAP_EVERY ASM_CASES_TAC [`bit i (x:N word)`; `bit i (y:N word)`] THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
    SIMP_TAC[EXP_ADD; EXP_1; MOD_LT; DIVISION; EXP_EQ_0; ARITH_EQ;
             ARITH_RULE `x < n /\ y < n ==> x + y < n * 2`]] THEN
  ASM_CASES_TAC `i = 0` THEN
  ASM_SIMP_TAC[EXP; MOD_1; ADD_CLAUSES; CONJUNCT1 LE;
               EXP_EQ_0; ARITH_EQ] THEN
  SIMP_TAC[MOD_ADD_CASES; DIVISION; EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[GSYM NOT_LE] THEN
  MAP_EVERY ABBREV_TAC
   [`m = val(x:N word) MOD 2 EXP i`; `n = val(y:N word) MOD 2 EXP i`] THEN
  SUBGOAL_THEN `m < 2 EXP i /\ n < 2 EXP i` MP_TAC THENL
   [ASM_MESON_TAC[DIVISION; EXP_EQ_0; ARITH_RULE `~(2 = 0)`]; ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP i = 2 * 2 EXP(i - 1)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM(CONJUNCT2 EXP); ADD1; SUB_ADD; LE_1];
    ABBREV_TAC `j = i - 1` THEN
    REWRITE_TAC[COND_SWAP; NOT_LE] THEN ASM_ARITH_TAC]);;

let BIT_WORD_SUB = prove
 (`!x (y:N word) i.
        bit i (word_sub x y) <=>
        i < dimindex(:N) /\
        ((bit i x <=> bit i y) <=>
         ~(i = 0) /\
         (~bit (i - 1) x /\ bit (i - 1) y \/
          (~bit (i - 1) x \/ bit (i - 1) y) /\
          bit (i - 1) (word_sub x y)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_RULE
   `word_sub x y:N word = word_not(word_add (word_not x) y)`] THEN
  REWRITE_TAC[BIT_WORD_NOT] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [BIT_WORD_ADD] THEN
  ASM_SIMP_TAC[BIT_WORD_NOT; ARITH_RULE `i < n ==> i - 1 < n`] THEN
  REWRITE_TAC[TAUT `~((~p <=> q) <=> r) <=> ((p <=> q) <=> r)`]);;

let BIT_WORD_NEG = prove
 (`!(x:N word) i.
        bit i (word_neg x) <=>
        i < dimindex(:N) /\
        (bit i x <=> i = 0 \/ ~bit (i - 1) x /\ ~bit (i - 1) (word_neg x))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_RULE `word_neg x:N word = word_sub (word 0) x`] THEN
  GEN_REWRITE_TAC LAND_CONV [BIT_WORD_SUB] THEN
  REWRITE_TAC[BIT_WORD_0] THEN CONV_TAC TAUT);;

let BIT_WORD_ADD_CLAUSES = prove
 (`(!x (y:N word).
        bit 0 (word_add x y) <=> ~(bit 0 x <=> bit 0 y)) /\
   (!x (y:N word) i.
        bit (i + 1) (word_add x y) <=>
        i + 1 < dimindex(:N) /\
        ((bit (i + 1) x <=> bit (i + 1) y) <=>
         (bit i x /\ bit i y \/
          (bit i x \/ bit i y) /\ ~(bit i (word_add x y)))))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [BIT_WORD_ADD] THEN
  SIMP_TAC[DIMINDEX_GE_1; LE_1; ADD_SUB; ADD_EQ_0; ARITH_EQ]);;

let BIT_WORD_SUB_CLAUSES = prove
 (`(!x (y:N word).
        bit 0 (word_sub x y) <=> ~(bit 0 x <=> bit 0 y)) /\
   (!x (y:N word) i.
        bit (i + 1) (word_sub x y) <=>
        i + 1 < dimindex(:N) /\
        ((bit (i + 1) x <=> bit (i + 1) y) <=>
         (~bit i x /\ bit i y \/
          (~bit i x \/ bit i y) /\ bit i (word_sub x y))))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [BIT_WORD_SUB] THEN
  SIMP_TAC[DIMINDEX_GE_1; LE_1; ADD_SUB; ADD_EQ_0; ARITH_EQ]);;

let BIT_WORD_NEG_CLAUSES = prove
 (`(!(x:N word).
        bit 0 (word_neg x) = bit 0 x) /\
   (!(x:N word) i.
        bit (i + 1) (word_neg x) <=>
        i + 1 < dimindex(:N) /\
        (bit (i + 1) x <=> ~bit i x /\ ~bit i (word_neg x)))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [BIT_WORD_NEG] THEN
  SIMP_TAC[DIMINDEX_GE_1; LE_1; ADD_SUB; ADD_EQ_0; ARITH_EQ]);;

let LE_VAL_MOD_STEP = prove
 (`!(x:N word) (y:N word) i.
        (val x MOD 2 EXP (i + 1)) <= (val y MOD 2 EXP (i + 1)) <=>
        ~bit i x /\ bit i y \/
        (bit i x <=> bit i y) /\ val x MOD 2 EXP i <= val y MOD 2 EXP i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_MOD_STEP] THEN
  MAP_EVERY BOOL_CASES_TAC [`bit i (x:N word)`; `bit i (y:N word)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
  REWRITE_TAC[LE_ADD_LCANCEL; NOT_LE] THEN TRY(MATCH_MP_TAC LT_IMP_LE) THEN
  MATCH_MP_TAC(ARITH_RULE `x:num < y ==> x < y + z`) THEN
  SIMP_TAC[DIVISION; EXP_EQ_0; ARITH_EQ]);;

let LT_VAL_MOD_STEP = prove
 (`!(x:N word) (y:N word) i.
        (val x MOD 2 EXP (i + 1)) < (val y MOD 2 EXP (i + 1)) <=>
        ~bit i x /\ bit i y \/
        (bit i x <=> bit i y) /\ val x MOD 2 EXP i < val y MOD 2 EXP i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_MOD_STEP] THEN
  MAP_EVERY BOOL_CASES_TAC [`bit i (x:N word)`; `bit i (y:N word)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
  REWRITE_TAC[LT_ADD_LCANCEL; NOT_LT] THEN TRY(MATCH_MP_TAC LT_IMP_LE) THEN
  MATCH_MP_TAC(ARITH_RULE `x:num < y ==> x < y + z`) THEN
  SIMP_TAC[DIVISION; EXP_EQ_0; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Miscellaneous lemmas we don't want to keep regenerating. Many of them in  *)
(* any case need a little bit of manual effort.                              *)
(* ------------------------------------------------------------------------- *)

let WORD_ADD_0 = prove
 (`(!x:N word. word_add x (word 0) = x) /\
   (!x:N word. word_add (word 0) x = x)`,
  CONV_TAC WORD_RULE);;

let WORD_ADD_SYM = prove
 (`!x y:N word. word_add x y = word_add y x`,
  CONV_TAC WORD_RULE);;

let WORD_ADD_ASSOC = prove
 (`!x y z:N word. word_add x (word_add y z) =
                  word_add (word_add x y) z`,
  CONV_TAC WORD_RULE);;

let WORD_ADD_AC = prove
 (`word_add x y = word_add y x /\
   word_add (word_add x y) z = word_add x (word_add y z) /\
   word_add x (word_add y z) = word_add y (word_add x z)`,
  CONV_TAC WORD_RULE);;

let WORD_MUL_0 = prove
 (`(!x:N word. word_mul x (word 0) = word 0) /\
   (!x:N word. word_mul (word 0) x = word 0)`,
  CONV_TAC WORD_RULE);;

let WORD_MUL_SYM = prove
 (`!x y:N word. word_mul x y = word_mul y x`,
  CONV_TAC WORD_RULE);;

let WORD_MUL_ASSOC = prove
 (`!x y z:N word. word_mul x (word_mul y z) =
                  word_mul (word_mul x y) z`,
  CONV_TAC WORD_RULE);;

let WORD_MUL_AC = prove
 (`word_mul x y = word_mul y x /\
   word_mul (word_mul x y) z = word_mul x (word_mul y z) /\
   word_mul x (word_mul y z) = word_mul y (word_mul x z)`,
  CONV_TAC WORD_RULE);;

let WORD_SUB_0 = prove
 (`!x:N word. word_sub x (word 0) = x`,
  CONV_TAC WORD_RULE);;

let WORD_SUB_LZERO = prove
 (`!x:N word. word_sub (word 0) x = word_neg x`,
  CONV_TAC WORD_RULE);;

let WORD_SUB_EQ_0 = prove
 (`!x y:N word. word_sub x y = word 0 <=> x = y`,
  CONV_TAC WORD_RULE);;

let WORD_SUB_REFL = prove
 (`!x:N word. word_sub x x = word 0`,
  CONV_TAC WORD_RULE);;

let WORD_NEG_NEG = prove
 (`!x:N word. word_neg(word_neg x) = x`,
  CONV_TAC WORD_RULE);;

let WORD_NEG_0 = prove
 (`word_neg (word 0) = word 0`,
  CONV_TAC WORD_RULE);;

let WORD_NEG_SUB = prove
 (`!x y:N word. word_neg(word_sub x y) = word_sub y x`,
  CONV_TAC WORD_RULE);;

let WORD_NEG_EQ_0 = prove
 (`!x:N word. word_neg x = word 0 <=> x = word 0`,
  CONV_TAC WORD_RULE);;

let WORD_NOT_NOT = prove
 (`!x:N word. word_not(word_not x) = x`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_AND_REFL = prove
 (`!x:N word. word_and x x = x`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_AND_0 = prove
 (`(!x:N word. word_and x (word 0) = word 0) /\
   (!x:N word. word_and (word 0) x = word 0)`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_AND_NOT0 = prove
 (`(!x:N word. word_and x (word_not(word 0)) = x) /\
   (!x:N word. word_and (word_not(word 0)) x = x)`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_AND_SYM = prove
 (`!x y:N word. word_and x y = word_and y x`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_AND_ASSOC = prove
 (`!x y z:N word. word_and x (word_and y z) = word_and (word_and x y) z`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_OR_REFL = prove
 (`!x:N word. word_or x x = x`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_OR_0 = prove
 (`(!x:N word. word_or x (word 0) = x) /\
   (!x:N word. word_or (word 0) x = x)`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_OR_NOT0 = prove
 (`(!x:N word. word_or x (word_not(word 0)) = word_not(word 0)) /\
   (!x:N word. word_or (word_not(word 0)) x = word_not(word 0))`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_OR_SYM = prove
 (`!x y:N word. word_or x y = word_or y x`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_OR_ASSOC = prove
 (`!x y z:N word. word_or x (word_or y z) = word_or (word_or x y) z`,
  CONV_TAC WORD_BITWISE_RULE);;
let WORD_OR_EQ_0 = prove
 (`!x y:N word. word_or x y = word 0 <=> x = word 0 /\ y = word 0`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_NOT_AND = prove
 (`!x y:N word. word_not(word_and x y) = word_or (word_not x) (word_not y)`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_NOT_OR = prove
 (`!x y:N word. word_not(word_or x y) = word_and (word_not x) (word_not y)`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_XOR_EQ_0 = prove
 (`!x y:N word. word_xor x y = word 0 <=> x = y`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_XOR_0 = prove
 (`(!x:N word. word_xor x (word 0) = x) /\
   (!x:N word. word_xor (word 0) x = x)`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_XOR_NOT = prove
 (`(!x y:N word. word_xor (word_not x) y = word_not(word_xor x y)) /\
   (!x y:N word. word_xor x (word_not y) = word_not(word_xor x y))`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_XOR_NOT0 = prove
 (`(!x:N word. word_xor x (word_not(word 0)) = word_not x) /\
   (!x:N word. word_xor (word_not(word 0)) x = word_not x)`,
  REWRITE_TAC[WORD_XOR_NOT; WORD_XOR_0]);;

let WORD_XOR_REFL = prove
 (`!x:N word. word_xor x x = word 0`,
  REWRITE_TAC[WORD_XOR_EQ_0]);;

let WORD_XOR_SYM = prove
 (`!x y:N word. word_xor x y = word_xor y x`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_XOR_ASSOC = prove
 (`!x y z:N word. word_xor x (word_xor y z) = word_xor (word_xor x y) z`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_AND_1 = prove
 (`(!x:N word. word_and x (word 1) = if bit 0 x then word 1 else word 0) /\
   (!x:N word. word_and (word 1) x = if bit 0 x then word 1 else word 0)`,
  REWRITE_TAC[WORD_BITWISE_RULE
   `word_and (word 1:N word) x = word_and x (word 1)`] THEN
  GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_AND; BIT_WORD_1; BIT_WORD_0] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i = 0` THEN
  ASM_REWRITE_TAC[BIT_WORD_0] THEN SIMP_TAC[DIMINDEX_GE_1; LE_1]);;

let WORD_AND_1_BITVAL = prove
 (`(!x:N word. word_and (word 1) x = word(bitval(bit 0 x))) /\
   (!x:N word. word_and x (word 1) = word(bitval(bit 0 x)))`,
  REWRITE_TAC[bitval; WORD_AND_1] THEN MESON_TAC[]);;

let WORD_NOT_NEG = prove
 (`!x:N word. word_not(word_neg x) = word_sub x (word 1)`,
  GEN_TAC THEN REWRITE_TAC[WORD_NOT_AS_SUB] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let WORD_NOT_SUB = prove
 (`!x y:N word.
        word_not(word_sub x y) = word_add (word_not x) y`,
  REWRITE_TAC[WORD_NOT_AS_SUB] THEN CONV_TAC WORD_RULE);;

let WORD_NOT_ADD = prove
 (`!x y:N word.
        word_not(word_add x y) = word_add (word_not x) (word_neg y)`,
  REWRITE_TAC[WORD_NOT_AS_SUB] THEN CONV_TAC WORD_RULE);;

let VAL_WORD_SUB_EQ_0 = prove
 (`!x y:N word. val(word_sub x y) = 0 <=> val x = val y`,
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN REWRITE_TAC[VAL_EQ]);;

let VAL_EQ_MAX_ALT = prove
 (`!x:N word. val x = 2 EXP dimindex(:N) - 1 <=> x = word_not(word 0)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ;  VAL_WORD_NOT; VAL_WORD_0; SUB_0]);;

let VAL_EQ_MAX = prove
 (`!x:N word. val x = 2 EXP dimindex(:N) - 1 <=> word_not x = word 0`,
  REWRITE_TAC[VAL_EQ_MAX_ALT] THEN CONV_TAC WORD_BITWISE_RULE);;

let VAL_EQ_MAX_MASK = prove
 (`!x:N word. val x = 2 EXP dimindex(:N) - 1 <=> x = word_neg(word 1)`,
  REWRITE_TAC[WORD_NEG_1; VAL_EQ_MAX_ALT]);;

let VAL_WORD_OR_EQ_0 = prove
 (`!x y:N word. val(word_or x y) = 0 <=> val x = 0 /\ val y = 0`,
  REWRITE_TAC[VAL_EQ_0; WORD_OR_EQ_0]);;

let VAL_WORD_AND_EQ_MAX = prove
 (`!x y:N word.
        val(word_and x y) = 2 EXP dimindex(:N) - 1 <=>
        val x = 2 EXP dimindex(:N) - 1 /\
        val y = 2 EXP dimindex(:N) - 1`,
  REWRITE_TAC[VAL_EQ_MAX] THEN CONV_TAC WORD_BITWISE_RULE);;

let WORD_SHL_AND = prove
 (`!(v:N word) w n.
        word_shl (word_and v w) n =
        word_and (word_shl v n) (word_shl w n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_SHL; BIT_WORD_AND] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `bit (i - n) (v:N word)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `bit (i - n) (w:N word)` THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let WORD_USHR_AND = prove
 (`!(v:N word) w n.
        word_ushr (word_and v w) n =
        word_and (word_ushr v n) (word_ushr w n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_USHR; BIT_WORD_AND] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i + n < dimindex(:N)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN ASM_SIMP_TAC[BIT_TRIVIAL] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let WORD_SHL_OR = prove
 (`!(v:N word) w n.
        word_shl (word_or v w) n =
        word_or (word_shl v n) (word_shl w n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_SHL; BIT_WORD_OR] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `bit (i - n) (v:N word)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `bit (i - n) (w:N word)` THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let WORD_USHR_OR = prove
 (`!(v:N word) w n.
        word_ushr (word_or v w) n =
        word_or (word_ushr v n) (word_ushr w n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_USHR; BIT_WORD_OR] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i + n < dimindex(:N)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN ASM_SIMP_TAC[BIT_TRIVIAL] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let WORD_SHL_XOR = prove
 (`!(v:N word) w n.
        word_shl (word_xor v w) n =
        word_xor (word_shl v n) (word_shl w n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_SHL; BIT_WORD_XOR] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `bit (i - n) (v:N word)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `bit (i - n) (w:N word)` THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let WORD_USHR_XOR = prove
 (`!(v:N word) w n.
        word_ushr (word_xor v w) n =
        word_xor (word_ushr v n) (word_ushr w n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_USHR; BIT_WORD_XOR] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i + n < dimindex(:N)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN ASM_SIMP_TAC[BIT_TRIVIAL] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let WORD_ADD_XOR_GEN = prove
 (`!x y:N word.
        word_add x y = word_add (word_shl (word_and x y) 1) (word_xor x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; CONG; VAL_WORD_ADD; VAL_WORD_SHL] THEN
  CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXP_1; VAL_WORD_ADD_AND_XOR]);;

let WORD_ADD_OR_GEN = prove
 (`!x y:N word. word_add x y = word_add (word_and x y) (word_or x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; CONG; VAL_WORD_ADD; VAL_WORD_SHL] THEN
  CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_WORD_ADD_AND_OR]);;

let WORD_OR_XOR_GEN = prove
 (`!x y:N word. word_or x y = word_add (word_and x y) (word_xor x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; CONG; VAL_WORD_ADD] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[VAL_WORD_OR_AND_XOR]);;

let WORD_ADD_OR_EQ = prove
 (`!x y:N word. word_add x y = word_or x y <=> word_and x y = word 0`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[WORD_ADD_OR_GEN] THEN
  CONV_TAC WORD_RULE);;

let WORD_OR_XOR_EQ = prove
 (`!x y:N word. word_or x y = word_xor x y <=> word_and x y = word 0`,
  REWRITE_TAC[WORD_OR_XOR_GEN] THEN CONV_TAC WORD_RULE);;

let WORD_ADD_OR = prove
 (`!x y:N word. word_and x y = word 0 ==> word_add x y = word_or x y`,
  REWRITE_TAC[WORD_ADD_OR_EQ]);;

let WORD_OR_XOR = prove
 (`!x y:N word. word_and x y = word 0 ==> word_or x y = word_xor x y`,
  REWRITE_TAC[WORD_OR_XOR_EQ]);;

let WORD_ADD_XOR = prove
 (`!x y:N word. word_and x y = word 0 ==> word_add x y = word_xor x y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[WORD_ADD_XOR_GEN] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE);;

let WORD_POPCOUNT_ADD_DISJOINT = prove
 (`!x y:N word.
        word_and x y = word 0
        ==> word_popcount(word_add x y) = word_popcount x + word_popcount y`,
  SIMP_TAC[WORD_ADD_OR; WORD_POPCOUNT_OR_DISJOINT]);;

let WORD_POPCOUNT_XOR_AND = prove
 (`!x y:N word.
        word_popcount(word_xor x y) + word_popcount(word_and x y) =
        word_popcount(word_or x y)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[GSYM WORD_POPCOUNT_ADD_DISJOINT; WORD_ADD_OR; WORD_BITWISE_RULE
   `word_and (word_xor x y) (word_and x y) = word 0`] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

let WORD_POPCOUNT_OR_AND = prove
 (`!x y:N word.
        word_popcount(word_or x y) + word_popcount(word_and x y) =
        word_popcount x + word_popcount y`,
  REWRITE_TAC[word_popcount; BITS_OF_WORD_OR; BITS_OF_WORD_AND] THEN
  SIMP_TAC[CARD_UNION_GEN; FINITE_BITS_OF_WORD; CARD_SUBSET; INTER_SUBSET;
           ARITH_RULE `x:num <= a ==> (a + b) - x + x = a + b`]);;

let WORD_POPCOUNT_XOR_AND2 = prove
 (`!x y:N word.
        word_popcount(word_xor x y) + 2 * word_popcount(word_and x y) =
        word_popcount x + word_popcount y`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM WORD_POPCOUNT_OR_AND] THEN
  REWRITE_TAC[GSYM WORD_POPCOUNT_XOR_AND] THEN ARITH_TAC);;

let WORD_POPCOUNT_XOR = prove
 (`!x y:N word.
      word_popcount(word_xor x y) <= word_popcount x + word_popcount y`,
  REWRITE_TAC[GSYM WORD_POPCOUNT_XOR_AND2; LE_ADD]);;

let WORD_SUB_XOR = prove
 (`!x y:N word.
        word_and (word_not x) y = word 0 ==> word_sub x y = word_xor x y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE `word_sub x y = z <=> word_add y z = x`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_ADD_XOR o lhand o snd) THEN
  ANTS_TAC THENL [POP_ASSUM MP_TAC; DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_XOR_SUB = prove
 (`!x y:N word.
        word_and (word_not x) y = word 0 ==> word_xor x y = word_sub x y`,
  SIMP_TAC[WORD_SUB_XOR]);;

let WORD_SUB_MASK_WORD = prove
 (`!k (x:N word).
        val x < 2 EXP k
        ==> word_sub (word(2 EXP k - 1)) x = word_xor (word(2 EXP k - 1)) x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WORD_SUB_XOR THEN
  SIMP_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0; BIT_WORD_NOT;
           BIT_MASK_WORD; TAUT `p ==> ~(q /\ r) <=> q /\ p ==> ~r`] THEN
  ASM_REWRITE_TAC[NOT_LT; BLOCK_BITS_ZERO; VAL_MOD_REFL]);;

let WORD_XOR_MASK_WORD = prove
 (`!k (x:N word).
        val x < 2 EXP k
        ==> word_xor (word(2 EXP k - 1)) x = word_sub (word(2 EXP k - 1)) x`,
  SIMP_TAC[WORD_SUB_MASK_WORD]);;

let WORD_XOR_INT_MIN = prove
 (`!w:N word. word_xor word_INT_MIN w = word_add word_INT_MIN w`,
  GEN_TAC THEN ONCE_REWRITE_TAC[WORD_ADD_XOR_GEN] THEN
  REWRITE_TAC[WORD_RULE `w:N word = word_add x w <=> x = word 0`] THEN
  REWRITE_TAC[WORD_SHL_AND] THEN
  MATCH_MP_TAC(WORD_BITWISE_RULE `x = word 0 ==> word_and x y = word 0`) THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_0; BIT_WORD_SHL; BIT_WORD_INT_MIN] THEN
  ARITH_TAC);;

let WORD_BITVAL_NOT = prove
 (`!b. word(bitval(~b)) = word_sub (word 1) (word(bitval b))`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_RULE);;

let IVAL_WORD_NOT = prove
 (`!x:N word. ival(word_not x) = --(ival x + &1)`,
  REWRITE_TAC[IVAL_IWORD_GALOIS] THEN
  REWRITE_TAC[INT_ARITH `--x:int <= --(y + &1) <=> y < x`] THEN
  REWRITE_TAC[INT_ARITH `--(x + &1):int < y <=> --y <= x`] THEN
  REWRITE_TAC[IVAL_BOUND] THEN
  REWRITE_TAC[IWORD_INT_NEG; IWORD_INT_ADD; IWORD_IVAL; GSYM WORD_IWORD] THEN
  CONV_TAC WORD_RULE);;

let [BIT_WORD_NEG_CASES; BIT_WORD_ADD_1_CASES; BIT_WORD_SUB_1_CASES] =
  (CONJUNCTS o prove)
 (`(!(x:N word) i.
        bit i (word_neg x) <=>
        i < dimindex(:N) /\
        (if ?j. j < i /\ bit j x then ~(bit i x) else bit i x)) /\
   (!(x:N word) i.
        bit i (word_add x (word 1)) <=>
        i < dimindex(:N) /\
        (if ?j. j < i /\ ~(bit j x) then bit i x else ~(bit i x))) /\
   (!(x:N word) i.
        bit i (word_sub x (word 1)) <=>
        i < dimindex(:N) /\
        (if ?j. j < i /\ bit j x then bit i x else ~(bit i x)))`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[LT; BIT_WORD_NEG_CLAUSES; BIT_WORD_ADD_CLAUSES;
              BIT_WORD_SUB_CLAUSES; ADD1; BIT_WORD_1] THEN
  SIMP_TAC[ADD_EQ_0; LE_1; DIMINDEX_GE_1; ARITH_EQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `i + 1 < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
  (ASM_CASES_TAC `i = 0` THEN ASM_SIMP_TAC[LT; LE_1; DIMINDEX_GE_1] THENL
   [CONV_TAC TAUT; ALL_TAC]) THEN
  ASM_CASES_TAC `bit i (x:N word)` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `bit (i + 1) (x:N word)` THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let BIT_WORD_AND_NEG = prove
 (`!(x:N word) i.
        bit i (word_and x (word_neg x)) <=>
        bit i x /\ !j. j < i ==> ~(bit j x)`,
  REWRITE_TAC[BIT_WORD_AND; BIT_WORD_NEG_CASES] THEN
  MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let BIT_WORD_OR_NEG = prove
 (`!(x:N word) i.
        bit i (word_or x (word_neg x)) <=>
        i < dimindex(:N) /\ ?j. j <= i /\ bit j x`,
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_NEG_CASES] THEN MESON_TAC[LE_LT]);;

let BIT_WORD_XOR_NEG = prove
 (`!(x:N word) i.
        bit i (word_xor x (word_neg x)) <=>
        i < dimindex(:N) /\ ?j. j < i /\ bit j x`,
  REWRITE_TAC[BIT_WORD_NEG_CASES; BIT_WORD_XOR] THEN MESON_TAC[]);;

let BIT_WORD_AND_ADD_1 = prove
 (`!(x:N word) i.
        bit i (word_and x (word_add x (word 1))) <=>
        bit i x /\ ?j. j < i /\ ~bit j x`,
  REWRITE_TAC[BIT_WORD_AND; BIT_WORD_ADD_1_CASES] THEN
  MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let BIT_WORD_AND_SUB_1 = prove
 (`!(x:N word) i.
        bit i (word_and x (word_sub x (word 1))) <=>
        bit i x /\ ?j. j < i /\ bit j x`,
  REWRITE_TAC[BIT_WORD_AND; BIT_WORD_SUB_1_CASES] THEN
  MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let BIT_WORD_OR_ADD_1 = prove
 (`!(x:N word) i.
        bit i (word_or x (word_add x (word 1))) <=>
        i < dimindex(:N) /\
        (bit i x \/ !j. j < i ==> bit j x)`,
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_ADD_1_CASES] THEN MESON_TAC[]);;

let BIT_WORD_OR_SUB_1 = prove
 (`!(x:N word) i.
        bit i (word_or x (word_sub x (word 1))) <=>
        i < dimindex(:N) /\
        (bit i x \/ !j. j < i ==> ~bit j x)`,
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SUB_1_CASES] THEN MESON_TAC[]);;

let BIT_WORD_XOR_ADD_1 = prove
 (`!(x:N word) i.
        bit i (word_xor x (word_add x (word 1))) <=>
        i < dimindex(:N) /\ !j. j < i ==> bit j x`,
  REWRITE_TAC[BIT_WORD_ADD_1_CASES; BIT_WORD_XOR] THEN MESON_TAC[]);;

let BIT_WORD_XOR_SUB_1 = prove
 (`!(x:N word) i.
        bit i (word_xor x (word_sub x (word 1))) <=>
        i < dimindex(:N) /\ !j. j < i ==> ~(bit j x)`,
   REWRITE_TAC[BIT_WORD_SUB_1_CASES; BIT_WORD_XOR] THEN MESON_TAC[]);;

let BIT_WORD_AND_NOT_SUB_1 = prove
 (`!(x:N word) i.
        bit i (word_and (word_not x) (word_sub x (word 1))) <=>
        i < dimindex(:N) /\ !j. j <= i ==> ~(bit j x)`,
  REWRITE_TAC[LE_LT; BIT_WORD_AND; BIT_WORD_NOT; BIT_WORD_SUB_1_CASES] THEN
  MESON_TAC[]);;

let BIT_WORD_AND_NOT_ADD_1 = prove
 (`!(x:N word) i.
        bit i (word_and (word_not x) (word_add x (word 1))) <=>
        i < dimindex(:N) /\
         ~(bit i x) /\ !j. j < i ==> bit j x`,
  REWRITE_TAC[BIT_WORD_AND; BIT_WORD_NOT; BIT_WORD_ADD_1_CASES] THEN
  MESON_TAC[]);;

let WORD_OR_SHL_USHR = prove
 (`!(h:N word) l m n.
        m + n = dimindex(:N)
        ==> word_or (word_shl h m) (word_ushr l n) =
            word_zx (word_ushr (word_join h l:(N tybit0)word) n)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[BIT_WORD_JOIN; BIT_WORD_ZX; BIT_WORD_SHL; BIT_WORD_USHR;
                  BIT_WORD_OR; DIMINDEX_TYBIT0] THEN
  SUBGOAL_THEN `m <= i <=> ~(i + n < dimindex(:N))` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[ARITH_RULE `i < n ==> i < 2 * n`] THEN
  MATCH_MP_TAC(TAUT `(p <=> s) /\ (q <=> F) /\ r ==> (p \/ q <=> r /\ s)`) THEN
  REPEAT CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC BIT_TRIVIAL THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let WORD_OR_USHR_SHL = prove
 (`!(h:N word) l m n.
        m + n = dimindex(:N)
        ==> word_or (word_ushr l m) (word_shl h n) =
            word_zx (word_ushr (word_join h l:(N tybit0)word) m)`,
  ONCE_REWRITE_TAC[ADD_SYM; WORD_OR_SYM] THEN
  REWRITE_TAC[WORD_OR_SHL_USHR]);;

let WORD_ADD_SHL_USHR = prove
 (`!(h:N word) l m n.
        m + n = dimindex(:N)
        ==> word_add (word_shl h m) (word_ushr l n) =
            word_zx (word_ushr (word_join h l:(N tybit0)word) n)`,
   REPEAT STRIP_TAC THEN
   W(MP_TAC o PART_MATCH (lhand o rand) WORD_ADD_OR o lhand o snd) THEN
   ASM_SIMP_TAC[WORD_OR_SHL_USHR] THEN DISCH_THEN MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
   X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   REWRITE_TAC[BIT_WORD_0; BIT_WORD_AND; BIT_WORD_SHL; BIT_WORD_USHR] THEN
   STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP (MESON[BIT_TRIVIAL]
    `bit i (x:N word) ==> ~(dimindex(:N) <= i)`))) THEN
   ASM_ARITH_TAC);;

let WORD_ADD_USHR_SHL = prove
 (`!(h:N word) l m n.
        m + n = dimindex(:N)
        ==> word_add (word_ushr l m) (word_shl h n) =
            word_zx (word_ushr (word_join h l:(N tybit0)word) m)`,
  ONCE_REWRITE_TAC[ADD_SYM; WORD_ADD_SYM] THEN
  REWRITE_TAC[WORD_ADD_SHL_USHR]);;

(* ------------------------------------------------------------------------- *)
(* An idiom for describing a mask duplicating a bit throughout a word.       *)
(* ------------------------------------------------------------------------- *)

let WORD_MASK_ALT = prove
 (`!p. word_neg(word(bitval p)) = if p then word_neg(word 1) else word 0`,
  MATCH_MP_TAC bool_INDUCT THEN
  REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0]);;

let WORD_MASK = prove
 (`!p. word_neg(word(bitval p)) = if p then word_not(word 0) else word 0`,
  REWRITE_TAC[WORD_MASK_ALT; WORD_NEG_1]);;

let BIT_WORD_MASK = prove
 (`!p i. bit i (word_neg(word(bitval p)):N word) <=> i < dimindex(:N) /\ p`,
  MATCH_MP_TAC bool_INDUCT THEN
  REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; BIT_WORD_0] THEN
  REWRITE_TAC[WORD_NEG_1; BIT_WORD_NOT; BIT_WORD_0]);;

let WORD_ISHR_MSB = prove
 (`!x:N word. word_ishr x (dimindex(:N) - 1) =
              word_neg(word(bitval(bit (dimindex(:N) - 1) x)))`,
  SIMP_TAC[WORD_EQ_BITS_ALT; BIT_WORD_MASK; BIT_WORD_ISHR] THEN
  SIMP_TAC[ARITH_RULE `i < n ==> (i + n - 1 < n <=> i = 0)`] THEN
  REWRITE_TAC[COND_ID; ADD_CLAUSES]);;

let WORD_NOT_MASK = prove
 (`!p. word_not(word_neg(word(bitval p))) = word_neg(word(bitval(~p)))`,
  MATCH_MP_TAC bool_INDUCT THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_RULE);;

let WORD_AND_MASK = prove
 (`(!p x. word_and (word_neg(word(bitval p))) x =
          if p then x else word 0) /\
   (!p x. word_and x (word_neg(word(bitval p))) =
          if p then x else word 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_MASK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_OR_MASK = prove
 (`(!p x. word_or (word_neg(word(bitval p))) x =
          if p then word_neg(word(bitval p)) else x) /\
   (!p x. word_or x (word_neg(word(bitval p))) =
          if p then word_neg(word(bitval p)) else x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_MASK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_XOR_MASK = prove
 (`(!p x. word_xor (word_neg(word(bitval p))) x =
          if p then word_not x else x) /\
   (!p x. word_xor x (word_neg(word(bitval p))) =
          if p then word_not x else x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_MASK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_NEG_AND_MASK = prove
 (`(!b x. word_neg (word_and (word_neg(word(bitval b))) x) =
          word_and (word_neg(word(bitval b))) (word_neg x)) /\
   (!b x. word_neg (word_and x (word_neg(word(bitval b)))) =
          word_and (word_neg x) (word_neg(word(bitval b))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_AND_MASK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_NEG_0]);;

let WORD_AND_MASKS = prove
 (`!p q. word_and (word_neg(word(bitval p))) (word_neg(word(bitval q))) =
         word_neg(word(bitval(p /\ q)))`,
  REPEAT(MATCH_MP_TAC bool_INDUCT THEN CONJ_TAC) THEN
  REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; WORD_AND_0; WORD_AND_REFL]);;

let WORD_OR_MASKS = prove
 (`!p q. word_or (word_neg(word(bitval p))) (word_neg(word(bitval q))) =
         word_neg(word(bitval(p \/ q)))`,
  REPEAT(MATCH_MP_TAC bool_INDUCT THEN CONJ_TAC) THEN
  REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; WORD_OR_0; WORD_OR_REFL]);;

let WORD_XOR_MASKS = prove
 (`!p q. word_xor (word_neg(word(bitval p))) (word_neg(word(bitval q))) =
         word_neg(word(bitval(~(p <=> q))))`,
  REPEAT(MATCH_MP_TAC bool_INDUCT THEN CONJ_TAC) THEN
  REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; WORD_XOR_0; WORD_XOR_REFL]);;

let WORD_AND_CONDITIONS = prove
 (`!p q. word_and (word(bitval p)) (word(bitval q)) =
         word(bitval(p /\ q))`,
  REPEAT(MATCH_MP_TAC bool_INDUCT THEN CONJ_TAC) THEN
  REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; WORD_AND_0; WORD_AND_REFL]);;

let WORD_OR_CONDITIONS = prove
 (`!p q. word_or (word(bitval p)) (word(bitval q)) =
         word(bitval(p \/ q))`,
  REPEAT(MATCH_MP_TAC bool_INDUCT THEN CONJ_TAC) THEN
  REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; WORD_OR_0; WORD_OR_REFL]);;

let WORD_XOR_CONDITIONS = prove
 (`!p q. word_xor (word(bitval p)) (word(bitval q)) =
         word(bitval(~(p <=> q)))`,
  REPEAT(MATCH_MP_TAC bool_INDUCT THEN CONJ_TAC) THEN
  REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; WORD_XOR_0; WORD_XOR_REFL]);;

let VAL_WORD_MASK = prove
 (`!b. val(word_neg(word(bitval b):N word)) =
       (2 EXP dimindex(:N) - 1) * bitval b`,
  GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_NEG_CASES; VAL_WORD_BITVAL; BITVAL_EQ_0] THEN
  REWRITE_TAC[COND_SWAP] THEN
  COND_CASES_TAC THEN  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  ARITH_TAC);;

let IVAL_WORD_MASK = prove
 (`!b. ival(word_neg(word(bitval b):N word)) = --(&(bitval b))`,
  GEN_TAC THEN REWRITE_TAC[WORD_IWORD; GSYM IWORD_INT_NEG] THEN
  MATCH_MP_TAC IVAL_IWORD THEN MATCH_MP_TAC(INT_ARITH
   `&0:int <= x /\ x <= &1 /\ &2 pow 0 <= e ==> --e <= --x /\ --x < e`) THEN
  REWRITE_TAC[INT_OF_NUM_LE; LE_0; BITVAL_BOUND] THEN
  MATCH_MP_TAC INT_POW_MONO THEN REWRITE_TAC[INT_OF_NUM_LE] THEN ARITH_TAC);;

let INT_VAL_WORD_MASK = prove
 (`!b. &(val(word_neg(word(bitval b):N word))):int =
       (&2 pow dimindex(:N) - &1) * &(bitval b)`,
  GEN_TAC THEN
  REWRITE_TAC[INT_VAL_WORD_NEG_CASES; VAL_WORD_BITVAL; BITVAL_EQ_0;
              INT_OF_NUM_EQ; COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  INT_ARITH_TAC);;

let REAL_VAL_WORD_MASK = prove
 (`!b. &(val(word_neg(word(bitval b):N word))):real =
       (&2 pow dimindex(:N) - &1) * &(bitval b)`,
  GEN_TAC THEN
  REWRITE_TAC[REAL_VAL_WORD_NEG_CASES; VAL_WORD_BITVAL; BITVAL_EQ_0;
              REAL_OF_NUM_EQ; COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  REAL_ARITH_TAC);;

let WORD_MUL_EXPAND_ALT = prove
 (`!x y:N word.
        word_mul x y =
        word(nsum {i | i < dimindex(:N)}
                  (\i. val(word_and (word_neg(word(bitval(bit i x))))
                                    (word_shl y i))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_MUL_EXPAND] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC NSUM_EQ THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES; WORD_VAL; VAL_WORD_0]);;

let WORD_SX_ZX_GEN = prove
 (`!x. (word_sx:M word->N word) x =
       word_or (word_shl (word_neg(word(bitval(bit (dimindex(:M)-1) x))))
                         (dimindex(:M)))
               (word_zx x)`,
  GEN_TAC THEN ASM_CASES_TAC `dimindex(:N) <= dimindex(:M)` THEN
  ASM_SIMP_TAC[WORD_SX_ZX; WORD_SHL_TRIVIAL; WORD_OR_0] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
  ASM_SIMP_TAC[GSYM IVAL_CONG; IVAL_WORD_SX; LT_IMP_LE] THEN
  REWRITE_TAC[IVAL_VAL; INTEGER_RULE
   `(x:int == y - p * z) (mod p) <=> (x == y) (mod p)`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_OR_DISJOINT o
    rand o rand o rator o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_SHL; BIT_WORD_ZX;
                BIT_WORD_MASK; BIT_WORD_0] THEN
    ONCE_REWRITE_TAC[BIT_GUARD] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[VAL_WORD_ZX; LT_IMP_LE] THEN
  REWRITE_TAC[VAL_WORD_SHL; GSYM INT_OF_NUM_CLAUSES;
              GSYM INT_OF_NUM_REM; INT_VAL_WORD_MASK] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE);;

let BIT_WORD_SX = prove
 (`!x i. bit i ((word_sx:M word->N word) x) <=>
         i < dimindex(:N) /\ bit (MIN i (dimindex(:M) - 1)) x`,
  REPEAT GEN_TAC THEN SIMP_TAC[DIMINDEX_NONZERO; ARITH_RULE
    `~(n = 0) ==> MIN i (n - 1) = if i < n then i else n - 1`] THEN
  REWRITE_TAC[WORD_SX_ZX_GEN; BIT_WORD_OR; BIT_WORD_SHL;
              BIT_WORD_MASK; BIT_WORD_ZX] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  ONCE_REWRITE_TAC[BIT_GUARD] THEN
  REWRITE_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`; DIMINDEX_NONZERO] THEN
  ASM_CASES_TAC `bit (dimindex(:M) - 1) (x:M word)` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Some lemmas about masks 000..001111..1111 and their values.               *)
(* ------------------------------------------------------------------------- *)

let VAL_WORD_AND_MASK = prove
 (`!(x:N word) k.
        val(word_and x (word_of_bits {i | i < k})) = val x MOD (2 EXP k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[val_def] THEN
  SIMP_TAC[BINARY_DIGITSUM_MOD; FINITE_NUMSEG_LT; NSUM_RESTRICT_SET] THEN
  MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM; BIT_WORD_AND; IN_ELIM_THM; BIT_WORD_OF_BITS] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[bitval] THEN ARITH_TAC);;

let IVAL_WORD_AND_MASK = prove
 (`!(x:N word) k.
        k < dimindex(:N)
        ==> ival(word_and x (word_of_bits {i | i < k})) =
            ival x rem (&2 pow k)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INT_REM_IVAL; LT_IMP_LE] THEN
  REWRITE_TAC[GSYM VAL_WORD_AND_MASK; ival] THEN
  MATCH_MP_TAC(MESON[] `p ==> (if p then x else y) = x`) THEN
  REWRITE_TAC[VAL_WORD_AND_MASK] THEN TRANS_TAC LTE_TRANS `2 EXP k` THEN
  SIMP_TAC[DIVISION; EXP_EQ_0; ARITH_EQ; LE_EXP] THEN ASM_ARITH_TAC);;

let VAL_WORD_AND_MASK_WORD = prove
 (`!x k. val(word_and x (word(2 EXP k - 1))) = val x MOD 2 EXP k`,
  REWRITE_TAC[GSYM WORD_OF_BITS_MASK; VAL_WORD_AND_MASK]);;

let WORD_AND_MASK_WORD = prove
 (`(!(x:N word) k.
        word_and x (word(2 EXP k - 1)) = word(val x MOD 2 EXP k)) /\
   (!(x:N word) k.
        word_and (word(2 EXP k - 1)) x = word(val x MOD 2 EXP k))`,
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [WORD_AND_SYM] THEN
  REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_AND_MASK_WORD] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  MATCH_MP_TAC(ARITH_RULE `x MOD n <= x /\ x < e ==> x MOD n < e`) THEN
  REWRITE_TAC[MOD_LE; VAL_BOUND]);;

let VAL_WORD_AND_NOT_MASK_WORD = prove
 (`!(x:N word) k.
        val(word_and x (word_not(word(2 EXP k - 1)))) =
        2 EXP k * val x DIV 2 EXP k`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`x:N word`; `k:num`] VAL_WORD_AND_MASK_WORD) THEN
  MATCH_MP_TAC(ARITH_RULE `h + l:num = h' + l' ==> l = l' ==> h = h'`) THEN
  REWRITE_TAC[DIVISION_SIMP] THEN
  W(MP_TAC o PART_MATCH (rand o rand) VAL_WORD_OR_DISJOINT o lhand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC WORD_BITWISE_RULE; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

let WORD_AND_NOT_MASK_WORD = prove
 (`(!(x:N word) k.
        word_and x (word_not(word(2 EXP k - 1))) =
        word(2 EXP k * val x DIV 2 EXP k)) /\
   (!(x:N word) k.
        word_and (word_not(word(2 EXP k - 1))) x =
        word(2 EXP k * val x DIV 2 EXP k))`,
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [WORD_AND_SYM] THEN
  REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_AND_NOT_MASK_WORD] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  REWRITE_TAC[GSYM VAL_WORD_AND_NOT_MASK_WORD; VAL_BOUND]);;

let WORD_BITMASK = prove
 (`!k. word_of_bits {i | i < k}:N word =
       word_sub (word_of_bits {k}) (word 1)`,
  REWRITE_TAC[WORD_OF_BITS_MASK; WORD_OF_BITS_SING_AS_WORD] THEN
  REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ]);;

let MASK_WORD_SUB = prove
 (`!k. word_sub (word(2 EXP k)) (word 1):N word = word(2 EXP k - 1)`,
  GEN_TAC THEN REWRITE_TAC[WORD_SUB] THEN
  REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ]);;

let WORD_AND_MASK_WORDS = prove
 (`!j k. word_and (word(2 EXP j - 1)) (word(2 EXP k - 1)):N word =
         word(2 EXP MIN j k - 1)`,
  SIMP_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_MASK_WORD] THEN ARITH_TAC);;

let WORD_OR_MASK_WORDS = prove
 (`!j k. word_or (word(2 EXP j - 1)) (word(2 EXP k - 1)):N word =
         word(2 EXP MAX j k - 1)`,
  SIMP_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OR; BIT_MASK_WORD] THEN ARITH_TAC);;

let WORD_USHR_MASK_WORD = prove
 (`!k i. k <= dimindex(:N)
         ==> word_ushr (word(2 EXP k - 1):N word) i = word(2 EXP (k - i) - 1)`,
  SIMP_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_MASK_WORD] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Trailing and leading zero count (returning word size for zero input).     *)
(* ------------------------------------------------------------------------- *)

let word_ctz = new_definition
 `word_ctz (a:N word) =
        if a = word 0 then dimindex(:N) else minimal i. bit i a`;;

let word_clz = new_definition
 `word_clz (a:N word) = dimindex(:N) - minimal m. !i. m <= i ==> ~bit i a`;;

let WORD_CLZ = prove
 (`!x:N word. word_clz x = dimindex (:N) - (minimal m. val x < 2 EXP m)`,
  GEN_TAC THEN REWRITE_TAC[word_clz] THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `m:num` THEN REWRITE_TAC[] THEN
  SIMP_TAC[GSYM WORD_USHR_EQ_0; WORD_EQ_BITS; BIT_WORD_USHR; BIT_WORD_0] THEN
  MESON_TAC[LE_EXISTS; ADD_SYM]);;

let WORD_CTZ_0 = prove
 (`word_ctz(word 0:N word) = dimindex(:N)`,
  REWRITE_TAC[word_ctz]);;

let WORD_LE_CTZ = prove
 (`!(a:N word) n.
        n <= word_ctz a <=> n <= dimindex(:N) /\ !i. bit i a ==> n <= i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_ctz] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BIT_WORD_0] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_EQ_BITS_ALT; BIT_WORD_0]) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) LE_MINIMAL o lhand o snd) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_MESON_TAC[NOT_LE; LE_CASES; LE_TRANS]);;

let WORD_CTZ_LE = prove
 (`!(a:N word) n.
        word_ctz a <= n <=> n < dimindex(:N) ==> ?i. i <= n /\ bit i a`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `m <= n <=> ~(SUC n <= m)`] THEN
  REWRITE_TAC[WORD_LE_CTZ; DE_MORGAN_THM] THEN
  REWRITE_TAC[ARITH_RULE `SUC n <= m <=> ~(m <= n)`] THEN
  MESON_TAC[NOT_LT]);;

let WORD_CTZ_LE_DIMINDEX = prove
 (`!a:N word. word_ctz(a) <= dimindex(:N)`,
  REWRITE_TAC[WORD_CTZ_LE; LT_REFL]);;

let WORD_CTZ_LBOUND = prove
 (`!(a:N word) i. bit i a ==> word_ctz(a) <= i`,
  REWRITE_TAC[WORD_CTZ_LE] THEN MESON_TAC[LE_REFL]);;

let WORD_CTZ_EQ_DIMINDEX = prove
 (`!a:N word. word_ctz a = dimindex(:N) <=> a = word 0`,
  REWRITE_TAC[GSYM LE_ANTISYM; WORD_CTZ_LE_DIMINDEX; WORD_LE_CTZ] THEN
  REWRITE_TAC[LE_REFL; WORD_EQ_BITS_ALT; BIT_WORD_0] THEN MESON_TAC[NOT_LE]);;

let WORD_CTZ_LT_DIMINDEX = prove
 (`!a:N word. word_ctz a < dimindex(:N) <=> ~(a = word 0)`,
  REWRITE_TAC[LT_LE; WORD_CTZ_LE_DIMINDEX; WORD_CTZ_EQ_DIMINDEX]);;

let WORD_CTZ_EQ_0 = prove
 (`!a:N word. word_ctz a = 0 <=> bit 0 a`,
  REWRITE_TAC[GSYM(CONJUNCT1 LE)] THEN
  REWRITE_TAC[WORD_CTZ_LE; CONJUNCT1 LE; UNWIND_THM2] THEN
  SIMP_TAC[DIMINDEX_GE_1; LE_1]);;

let WORD_CTZ_UNIQUE_GEN = prove
 (`!(a:N word) n.
        word_ctz a = n <=>
        n <= dimindex(:N) /\
        (n < dimindex(:N) ==> bit n a) /\
        (!i. i < n ==> ~bit i a)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM LE_ANTISYM] THEN
  REWRITE_TAC[WORD_CTZ_LE; WORD_LE_CTZ] THEN
  ASM_CASES_TAC `n <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NOT_LT; MESON[] `p ==> ~bit a b <=> bit a b ==> ~p`] THEN
  ASM_CASES_TAC `n < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[LE_ANTISYM]);;

let WORD_CTZ_UNIQUE = prove
 (`!(a:N word) n.
        n < dimindex(:N)
        ==> (word_ctz a = n <=> bit n a /\ !i. i < n ==> ~bit i a)`,
  SIMP_TAC[WORD_CTZ_UNIQUE_GEN; LT_IMP_LE]);;

let WORD_LE_CTZ_VAL_MOD = prove
 (`!(a:N word) n.
        n <= word_ctz a <=>
        n <= dimindex(:N) /\ val a MOD 2 EXP n = 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_LE_CTZ] THEN
  ASM_CASES_TAC `n <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[VAL_MOD; NOT_LE] THEN
  SIMP_TAC[NSUM_EQ_0_IFF; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH_EQ; BITVAL_EQ_0]);;

let WORD_LE_CTZ_VAL = prove
 (`!(a:N word) n.
        n <= word_ctz a <=>
        n <= dimindex(:N) /\ 2 EXP n divides val a`,
  REWRITE_TAC[WORD_LE_CTZ_VAL_MOD] THEN
  MESON_TAC[divides; MOD_EQ_0; MULT_SYM]);;

let WORD_CTZ_UNIQUE_VAL = prove
 (`!(a:N word) n.
        val a MOD (2 EXP (n + 1)) = 2 EXP n
        ==> word_ctz a = n`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `dimindex(:N)` o MATCH_MP
   (ARITH_RULE `a MOD p = n
                ==> !e. a MOD p <= a ==> a < 2 EXP e ==> n < 2 EXP e`)) THEN
  REWRITE_TAC[VAL_BOUND; MOD_LE; LT_EXP; ARITH] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[WORD_CTZ_UNIQUE] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[BIT_VAL_MOD; LE_REFL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x MOD (2 EXP n)`) THEN
  REWRITE_TAC[EXP_ADD; MOD_MOD; MOD_REFL] THEN
  REWRITE_TAC[GSYM VAL_WORD_AND_MASK] THEN
  REWRITE_TAC[VAL_EQ_0; WORD_EQ_BITS; BIT_WORD_0] THEN
  REWRITE_TAC[BIT_WORD_AND; BIT_WORD_OF_BITS; IN_ELIM_THM] THEN
  ASM_MESON_TAC[LT_TRANS]);;

let WORD_CLZ_0 = prove
 (`word_clz(word 0:N word) = dimindex(:N)`,
  REWRITE_TAC[word_clz; BIT_WORD_0] THEN
  MATCH_MP_TAC(ARITH_RULE `d = 0 ==> m - d = m`) THEN
  MATCH_MP_TAC MINIMAL_UNIQUE THEN REWRITE_TAC[LT]);;

let WORD_SIZE_SUB_CLZ = prove
 (`!(a:N word).
        dimindex(:N) - word_clz(a) = (minimal m. !i. m <= i ==> ~bit i a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_clz] THEN
  MATCH_MP_TAC(ARITH_RULE `m:num <= n ==> n - (n - m) = m`) THEN
  MATCH_MP_TAC MINIMAL_UBOUND THEN MESON_TAC[BIT_TRIVIAL]);;

let WORD_CLZ_LE_DIMINDEX = prove
 (`!a:N word. word_clz(a) <= dimindex(:N)`,
  REWRITE_TAC[word_clz] THEN ARITH_TAC);;

let WORD_LE_CLZ = prove
 (`!(a:N word) n.
        n <= word_clz(a) <=>
        n <= dimindex(:N) /\ !i. bit i a ==> i + n < dimindex(:N)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n <= dimindex(:N)` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[WORD_CLZ_LE_DIMINDEX; LE_TRANS]] THEN
  TRANS_TAC EQ_TRANS
   `dimindex(:N) - word_clz(a:N word) <= dimindex(:N) - n` THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[WORD_SIZE_SUB_CLZ]] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MINIMAL_LE o lhand o snd) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MESON_TAC[BIT_TRIVIAL]; DISCH_THEN SUBST1_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `p ==> ~q <=> q ==> ~p`] THEN
  REWRITE_TAC[NOT_LE; MESON[LE_REFL; LTE_TRANS]
   `(?m:num. m <= n /\ !i. P i ==> i < m) <=> (!i. P i ==> i < n)`] THEN
  ASM_SIMP_TAC[ARITH_RULE `n:num <= d ==> (i < d - n <=> i + n < d)`]);;

let WORD_CLZ_LE = prove
 (`!(a:N word) n.
        word_clz(a) <= n <=>
        n < dimindex(:N) ==> ?i. dimindex(:N) <= i + n + 1 /\ bit i a`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `m <= n <=> ~(SUC n <= m)`] THEN
  REWRITE_TAC[WORD_LE_CLZ; DE_MORGAN_THM] THEN REWRITE_TAC[LE_SUC_LT] THEN
  ASM_CASES_TAC `n < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_LT] THEN
  MESON_TAC[ARITH_RULE `i + SUC n = i + n + 1`]);;

let WORD_CLZ_LBOUND_ALT = prove
 (`!(a:N word) i. bit i a ==> word_clz(a) + i < dimindex(:N)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ARITH_RULE
   `~(n <= i) /\ c <= (n - 1) - i ==> c + i < n`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[BIT_TRIVIAL]; ALL_TAC] THEN
  REWRITE_TAC[WORD_CLZ_LE] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `i:num` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let WORD_CLZ_LBOUND = prove
 (`!(a:N word) i. bit i a ==> word_clz(a) < dimindex(:N) - i`,
  MESON_TAC[WORD_CLZ_LBOUND_ALT; ARITH_RULE `a + i:num < n ==> a < n - i`]);;

let WORD_CLZ_EQ_DIMINDEX = prove
 (`!a:N word. word_clz a = dimindex(:N) <=> a = word 0`,
  REWRITE_TAC[GSYM LE_ANTISYM; WORD_CLZ_LE_DIMINDEX; WORD_LE_CLZ] THEN
  REWRITE_TAC[LE_REFL; ARITH_RULE `~(i + n:num < n)`] THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_0]);;

let WORD_CLZ_LT_DIMINDEX = prove
 (`!a:N word. word_clz a < dimindex(:N) <=> ~(a = word 0)`,
  REWRITE_TAC[LT_LE; WORD_CLZ_LE_DIMINDEX; WORD_CLZ_EQ_DIMINDEX]);;

let WORD_CLZ_EQ_0 = prove
 (`!a:N word. word_clz a = 0 <=> bit (dimindex(:N) - 1) a`,
  REWRITE_TAC[GSYM(CONJUNCT1 LE)] THEN
  REWRITE_TAC[WORD_CLZ_LE; CONJUNCT1 LE; UNWIND_THM2] THEN
  GEN_TAC THEN SIMP_TAC[DIMINDEX_GE_1; LE_1; ADD_CLAUSES] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MESON[BIT_TRIVIAL]
   `bit i (a:N word) <=> ~(dimindex(:N) <= i) /\ bit i a`] THEN
  REWRITE_TAC[CONJ_ASSOC; DIMINDEX_GE_1; UNWIND_THM2; ARITH_RULE
   `n <= i + 1 /\ ~(n <= i) <=> i = n - 1 /\ 1 <= n`]);;

let WORD_CLZ_DECOMP = prove
 (`!a:N word.
        word_clz(a) + (minimal m. !i. m <= i ==> ~bit i a) = dimindex(:N)`,
  GEN_TAC THEN REWRITE_TAC[word_clz] THEN
  MATCH_MP_TAC SUB_ADD THEN MATCH_MP_TAC MINIMAL_UBOUND THEN
  MESON_TAC[BIT_TRIVIAL]);;

let WORD_CLZ_UNIQUE_GEN = prove
 (`!(a:N word) n.
        word_clz a = n <=>
        n <= dimindex(:N) /\
        (n < dimindex(:N) ==> bit (dimindex(:N) - n - 1) a) /\
        (!i. dimindex(:N) - n <= i ==> ~bit i a)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM LE_ANTISYM] THEN
  REWRITE_TAC[WORD_CLZ_LE; WORD_LE_CLZ] THEN
  ASM_CASES_TAC `n <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NOT_LT; MESON[] `p ==> ~bit a b <=> bit a b ==> ~p`] THEN
  ASM_SIMP_TAC[ARITH_RULE `n:num <= N ==> (~(N - n <= i) <=> i + n < N)`] THEN
  ASM_CASES_TAC `n < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(r ==> (p <=> q)) ==> (p /\ r <=> q /\ r)`) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[MATCH_MP
   (MESON[] `(!i. bit i a ==> P i)
             ==> (!i. bit i a <=> P i /\ bit i a)`) th]) THEN
  ASM_REWRITE_TAC[CONJ_ASSOC; DIMINDEX_GE_1; UNWIND_THM2; ARITH_RULE
   `N <= i + n + 1 /\ i + n < N <=> 1 <= N /\ n < N /\ i = N - n - 1`] THEN
  EQ_TAC THEN SIMP_TAC[] THEN ASM_ARITH_TAC);;

let WORD_CLZ_UNIQUE = prove
 (`!(a:N word) n.
        n < dimindex(:N)
        ==> (word_clz a = n <=>
             bit (dimindex(:N) - n - 1) a /\
             !i. dimindex(:N) - n <= i ==> ~bit i a)`,
  SIMP_TAC[WORD_CLZ_UNIQUE_GEN; LT_IMP_LE]);;

let WORD_LE_CLZ_VAL = prove
 (`!(a:N word) n.
        n <= word_clz a <=>
        n <= dimindex(:N) /\ val a < 2 EXP (dimindex(:N) - n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_LE_CLZ] THEN
  ASM_CASES_TAC `n <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `val(a:N word) DIV 2 EXP (dimindex(:N) - n) = 0` THEN
  CONJ_TAC THENL [ALL_TAC; SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ]] THEN
  REWRITE_TAC[VAL_DIV] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NSUM_EQ_0_IFF o rand o snd) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i | i < dimindex(:N)}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; MULT_EQ_0; EXP_EQ_0; ARITH_EQ; BITVAL_EQ_0] THEN
  ASSUME_TAC(SPEC `a:N word` BIT_TRIVIAL) THEN
  EQ_TAC THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  ASM_CASES_TAC `bit i (a:N word)` THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let WORD_LE_CLZ_VAL_MULT = prove
 (`!(a:N word) n.
        n <= word_clz a <=>
        n <= dimindex(:N) /\ 2 EXP n * val a < 2 EXP dimindex(:N)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_LE_CLZ_VAL] THEN
  ASM_CASES_TAC `n <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `2 EXP dimindex(:N) = 2 EXP n * 2 EXP (dimindex(:N) - n)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]]);;

let WORD_LE_CLZ_VAL_DIV = prove
 (`!(a:N word) n.
        n <= word_clz a <=>
        n <= dimindex(:N) /\ val a DIV (2 EXP (dimindex(:N) - n)) = 0`,
  SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ; WORD_LE_CLZ_VAL]);;

let VAL_BOUND_CLZ = prove
 (`!(a:N word) n.
        2 EXP n * val a < 2 EXP dimindex(:N) <=>
        a = word 0 \/ n <= word_clz a`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:N word = word 0` THEN
  ASM_REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; EXP_LT_0; EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[WORD_LE_CLZ_VAL_MULT] THEN
  REWRITE_TAC[TAUT `(p <=> q /\ p) <=> p ==> q`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
   `n * a < N ==> n * 1 <= n * a ==> n <= N`)) THEN
  REWRITE_TAC[LE_EXP; ARITH_EQ; EXP_EQ_0; LE_MULT_LCANCEL] THEN
  ASM_SIMP_TAC[LE_1; VAL_EQ_0]);;

let WORD_CLZ_UNIQUE_VAL = prove
 (`!(a:N word) n.
        n < dimindex(:N) /\
        val a DIV (2 EXP (dimindex(:N) - n - 1)) = 1
        ==> word_clz a = n`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WORD_CLZ_UNIQUE] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[BIT_VAL; ARITH]; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i = (dimindex (:N) - n - 1) + SUC(i - (dimindex(:N) - n))`
  SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[BIT_VAL; EXP_ADD; GSYM DIV_DIV] THEN
  MATCH_MP_TAC(MESON[ODD] `n = 0 ==> ~ODD n`) THEN
  SIMP_TAC[DIV_EQ_0; ARITH_EQ; EXP_EQ_0] THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `1 = 2 EXP 0`] THEN
  REWRITE_TAC[LT_EXP] THEN ARITH_TAC);;

let WORD_CTZ_BIT = prove
 (`!k. word_ctz (word_of_bits {k}:N word) = MIN k (dimindex(:N))`,
  GEN_TAC THEN REWRITE_TAC[WORD_CTZ_UNIQUE_GEN; BIT_WORD_OF_BITS; IN_SING] THEN
  REWRITE_TAC[ARITH_RULE `MIN k n = if k < n then k else n`] THEN
  ASM_MESON_TAC[LT_IMP_LE; LT_REFL; LE_REFL]);;

let WORD_CLZ_BIT = prove
 (`!k. word_clz (word_of_bits {k}:N word) =
       if k < dimindex(:N) then dimindex(:N) - 1 - k else dimindex(:N)`,
  GEN_TAC THEN REWRITE_TAC[WORD_CLZ_UNIQUE_GEN; BIT_WORD_OF_BITS; IN_SING] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let WORD_CTZ_MASK_WORD = prove
 (`!k. word_ctz (word(2 EXP k - 1):N word) = if k = 0 then dimindex(:N) else 0`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_CTZ_0; WORD_CTZ_EQ_0] THEN
  ASM_SIMP_TAC[BIT_MASK_WORD; DIMINDEX_GE_1; LE_1]);;

let WORD_CLZ_MASK_WORD = prove
 (`!k. word_clz (word(2 EXP k - 1):N word) = dimindex(:N) - k`,
  REWRITE_TAC[WORD_CLZ_UNIQUE_GEN; BIT_MASK_WORD] THEN ASM_ARITH_TAC);;

let WORD_AND_NEG_CTZ = prove
 (`!x:N word. word_and x (word_neg x) = word_of_bits {word_ctz x}`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[BIT_WORD_AND_NEG; BIT_WORD_OF_BITS; IN_SING] THEN
  MESON_TAC[WORD_CTZ_UNIQUE_GEN; LT_IMP_LE]);;

let WORD_XOR_SUB_1_CTZ = prove
 (`!x:N word.
        word_xor x (word_sub x (word 1)) =
        word(2 EXP (word_ctz x + 1) - 1)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_XOR_SUB_1; BIT_MASK_WORD] THEN
  SIMP_TAC[WORD_LE_CTZ; ARITH_RULE `a < b + 1 <=> a <= b`] THEN
  MESON_TAC[LT_IMP_LE; NOT_LT]);;

let WORD_AND_NOT_SUB_1_CTZ = prove
 (`!x:N word.
        word_and (word_not x) (word_sub x (word 1)) =
        word(2 EXP word_ctz x - 1)`,
  SIMP_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND_NOT_SUB_1; BIT_MASK_WORD] THEN
  REWRITE_TAC[GSYM NOT_LE; WORD_CTZ_LE] THEN MESON_TAC[NOT_LE]);;

let WORD_CTZ_EMULATION_REV = prove
 (`!x:N word.
        word_clz(word_and (word_not x) (word_sub x (word 1))) =
        dimindex(:N) - word_ctz x`,
  REWRITE_TAC[WORD_AND_NOT_SUB_1_CTZ; WORD_CLZ_MASK_WORD]);;

let WORD_CTZ_EMULATION_AND_NEG_REV = prove
 (`!x:N word.
     word_clz(word_and x (word_neg x)) =
     if x = word 0 then dimindex(:N) else dimindex(:N) - 1 - word_ctz x`,
  GEN_TAC THEN REWRITE_TAC[WORD_AND_NEG_CTZ; WORD_CLZ_BIT] THEN
  REWRITE_TAC[WORD_CTZ_LT_DIMINDEX; COND_SWAP] THEN ARITH_TAC);;

let WORD_CTZ_EMULATION_XOR_SUB_1_REV = prove
 (`!x:N word.
    word_clz(word_xor x (word_sub x (word 1))) = dimindex(:N) - 1 - word_ctz x`,
  GEN_TAC THEN REWRITE_TAC[WORD_XOR_SUB_1_CTZ; WORD_CLZ_MASK_WORD] THEN
  ARITH_TAC);;

let WORD_CTZ_EMULATION = prove
 (`!x:N word.
        word_ctz x =
        dimindex(:N) - word_clz(word_and (word_not x) (word_sub x (word 1)))`,
  GEN_TAC THEN MATCH_MP_TAC(ARITH_RULE
   `t:num <= n /\ l <= n /\ l = n - t ==> t = n - l`) THEN
  REWRITE_TAC[WORD_CLZ_LE_DIMINDEX; WORD_CTZ_LE_DIMINDEX] THEN
  REWRITE_TAC[WORD_CTZ_EMULATION_REV]);;

let WORD_CTZ_EMULATION_AND_NEG = prove
 (`!x:N word.
        word_ctz x =
        if x = word 0 then dimindex(:N)
        else dimindex(:N) - 1 - word_clz(word_and x (word_neg x))`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_CTZ_0] THEN
  ASM_REWRITE_TAC[WORD_CTZ_EMULATION_AND_NEG_REV] THEN
  ASM_SIMP_TAC[WORD_CTZ_LT_DIMINDEX; DIMINDEX_GE_1; ARITH_RULE
  `1 <= n ==> (c = n - 1 - (n - 1 - c) <=> c < n)`]);;

let WORD_CTZ_EMULATION_XOR_SUB_1 = prove
 (`!x:N word.
        word_ctz x =
        if x = word 0 then dimindex(:N)
        else dimindex(:N) - 1 - word_clz(word_xor x (word_sub x (word 1)))`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_CTZ_0] THEN
  REWRITE_TAC[WORD_CTZ_EMULATION_XOR_SUB_1_REV] THEN
  ASM_SIMP_TAC[WORD_CTZ_LT_DIMINDEX; DIMINDEX_GE_1; ARITH_RULE
  `1 <= n ==> (c = n - 1 - (n - 1 - c) <=> c < n)`]);;

let WORD_CLZ_IMP = prove
 (`!(x:N word) (y:N word).
        (!i. i < dimindex(:N) /\ bit i x ==> bit i y)
        ==> word_clz y <= word_clz x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(MESON[LE_TRANS; LE_REFL]
   `(!d:num. d <= x ==> d <= y) ==> x <= y`) THEN
  REWRITE_TAC[WORD_LE_CLZ] THEN ASM_MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let WORD_CLZ_OR = prove
 (`!(x:N word) y. word_clz (word_or x y) = MIN (word_clz x) (word_clz y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ARITH_RULE
   `p = MIN m n <=> p <= m /\ p <= n /\ (m <= p \/ n <= p)`] THEN
  SIMP_TAC[WORD_CLZ_IMP; BIT_WORD_OR_ALT] THEN
  MP_TAC(ISPEC `word_or x y:N word` WORD_LE_CLZ) THEN
  REWRITE_TAC[BIT_WORD_OR_ALT; FORALL_AND_THM;
              TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> (p /\ q) /\ (p /\ r)`] THEN
  SIMP_TAC[GSYM WORD_LE_CLZ] THEN ARITH_TAC);;

let WORD_CTZ_IMP = prove
 (`!(x:N word) (y:N word).
        (!i. i < dimindex(:N) /\ bit i x ==> bit i y)
        ==> word_ctz y <= word_ctz x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(MESON[LE_TRANS; LE_REFL]
   `(!d:num. d <= x ==> d <= y) ==> x <= y`) THEN
  REWRITE_TAC[WORD_LE_CTZ] THEN ASM_MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let WORD_CTZ_OR = prove
 (`!(x:N word) y. word_ctz (word_or x y) = MIN (word_ctz x) (word_ctz y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ARITH_RULE
   `p = MIN m n <=> p <= m /\ p <= n /\ (m <= p \/ n <= p)`] THEN
  SIMP_TAC[WORD_CTZ_IMP; BIT_WORD_OR_ALT] THEN
  MP_TAC(ISPEC `word_or x y:N word` WORD_LE_CTZ) THEN
  REWRITE_TAC[BIT_WORD_OR_ALT; FORALL_AND_THM;
              TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> (p /\ q) /\ (p /\ r)`] THEN
  SIMP_TAC[GSYM WORD_LE_CTZ] THEN ARITH_TAC);;

let WORD_CLZ_MONO = prove
 (`!(x:N word) (y:N word). val x <= val y ==> word_clz y <= word_clz x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(MESON[LE_TRANS; LE_REFL]
   `(!d:num. d <= x ==> d <= y) ==> x <= y`) THEN
  REWRITE_TAC[WORD_LE_CLZ_VAL] THEN ASM_ARITH_TAC);;

let WORD_CTZ_EMULATION_POPCOUNT = prove
 (`!x:N word.
        word_ctz x =
        word_popcount(word_and (word_not x) (word_sub x (word 1)))`,
  GEN_TAC THEN ASM_CASES_TAC `x:N word = word 0` THEN
  ASM_REWRITE_TAC[word_ctz; WORD_AND_REFL; WORD_POPCOUNT_NOT;
                  WORD_POPCOUNT_0; SUB_0; WORD_RULE
                    `word_sub (word 0) (word 1) = word_not(word 0)`] THEN
  REWRITE_TAC[word_popcount; bits_of_word; BIT_WORD_AND_NOT_SUB_1] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [WORD_EQ_BITS]) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; BIT_WORD_0] THEN
  GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN
  ABBREV_TAC `m = minimal i. bit i (x:N word)` THEN POP_ASSUM(K ALL_TAC) THEN
  STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM CARD_NUMSEG_LT] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  ASM_MESON_TAC[BIT_GUARD; LTE_TRANS; LT_TRANS; LE_REFL; NOT_LE]);;

(* ------------------------------------------------------------------------- *)
(* Reversal of the b-bit fields in an N-bit word. If N isn't a multiple      *)
(* of b, this leaves bits above the highest b multiple unchanged.            *)
(* ------------------------------------------------------------------------- *)

let word_reversefields = new_definition
 `(word_reversefields:num->(N)word->(N)word) (b:num) w =
  word_of_bits
    { i | i < dimindex(:N) /\
          bit (if i < b * dimindex(:N) DIV b
               then b * (dimindex(:N) DIV b - 1 - i DIV b) + i MOD b
               else i) w}`;;

let BIT_WORD_REVERSEFIELDS = prove
 (`!(x:(N)word) b i.
        bit i (word_reversefields b x) <=>
        i < dimindex(:N) /\
        bit (if i < b * dimindex(:N) DIV b
             then b * (dimindex(:N) DIV b - 1 - i DIV b) + i MOD b
             else i) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_reversefields; BIT_WORD_OF_BITS] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;

let WORD_REVERSEFIELDS_REVERSEFIELDS = prove
 (`!(x:(N)word) b. word_reversefields b (word_reversefields b x) = x`,
  ONCE_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[BIT_WORD_REVERSEFIELDS] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ_CASES_TAC(ARITH_RULE `b = 0 \/ 0 < b`) THEN
  ASM_REWRITE_TAC[MOD_ZERO; DIV_ZERO; MULT_CLAUSES; ADD_CLAUSES; LT] THEN
  ABBREV_TAC `q = dimindex (:N) DIV b` THEN
  ASM_CASES_TAC `i:num < b * q` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT; LE_1; DIV_MULT_ADD;
    MOD_MULT_ADD; MOD_MOD_REFL; DIV_LT; MOD_LT_EQ_LT; ADD_CLAUSES] THEN
  SUBGOAL_THEN `b * (q - 1 - i DIV b) + i MOD b < b * q` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE
     `m < n /\ n * (x + 1) <= n * q ==> n * x + m < n * q`) THEN
    ASM_REWRITE_TAC[MOD_LT_EQ_LT; LE_MULT_LCANCEL] THEN
    UNDISCH_TAC `i:num < b * q` THEN
    ASM_CASES_TAC `q = 0` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC(TAUT `p /\ (q <=> q') ==> (p /\ q <=> q')`) THEN CONJ_TAC THENL
   [TRANS_TAC LTE_TRANS `b * q:num` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`dimindex(:N)`; `b:num`] DIVISION) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    AP_THM_TAC THEN AP_TERM_TAC THEN
    TRANS_TAC EQ_TRANS `b * i DIV b + i MOD b` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[DIVISION_SIMP]] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `x < n ==> n - 1 - (n - 1 - x) = x`) THEN
    ASM_SIMP_TAC[RDIV_LT_EQ; LE_1] THEN ASM_ARITH_TAC]);;

let BIT_REVERSEFIELDS_1 = prove
 (`!(x:N word) i.
        bit i (word_reversefields 1 x) <=>
        i < dimindex(:N) /\ bit (dimindex(:N) - 1 - i) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIT_WORD_REVERSEFIELDS] THEN
  REWRITE_TAC[MULT_CLAUSES; DIV_1; MOD_1; ADD_CLAUSES] THEN
  MESON_TAC[]);;

let WORD_CTZ_REVERSEFIELDS = prove
 (`!x:N word. word_ctz(word_reversefields 1 x) = word_clz x`,
  GEN_TAC THEN REWRITE_TAC[MESON[LE_REFL; LE_ANTISYM]
   `a = b <=> !x:num. x <= a <=> x <= b`] THEN
  REWRITE_TAC[WORD_LE_CTZ; WORD_LE_CLZ] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[BIT_REVERSEFIELDS_1] THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)`) THEN
  DISCH_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `dimindex(:N) - 1 - i`) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [BIT_GUARD]) THEN
  ASM_SIMP_TAC[ARITH_RULE `i < n ==> n - 1 - (n - 1 - i) = i`] THEN
  ASM_ARITH_TAC);;

let WORD_CLZ_REVERSEFIELDS = prove
 (`!x:N word. word_clz(word_reversefields 1 x) = word_ctz x`,
  MESON_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS; WORD_CTZ_REVERSEFIELDS]);;

let WORD_CLZ_USHR = prove
 (`!(x:N word) n.
        word_clz (word_ushr x n) = MIN (dimindex(:N)) (word_clz x + n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_CLZ_UNIQUE_GEN; BIT_WORD_USHR] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `MIN a b < a <=> b < a`] THEN
  SIMP_TAC[ARITH_RULE
   `c + n < N ==> N - MIN N (c + n) - 1 + n = N - c - 1`] THEN
  REWRITE_TAC[ARITH_RULE
   `N - MIN N c <= i <=> N <= i + c`] THEN
  MP_TAC(ISPECL [`x:N word`; `word_clz(x:N word)`] WORD_CLZ_UNIQUE_GEN) THEN
  REWRITE_TAC[LE_REFL] THEN STRIP_TAC THEN CONJ_TAC THENL
   [DISCH_TAC; GEN_TAC THEN DISCH_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let WORD_SHL_AS_USHR = prove
 (`!(x:N word) n.
        word_shl x n =
        word_reversefields 1 (word_ushr (word_reversefields 1 x) n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[BIT_REVERSEFIELDS_1; BIT_WORD_SHL; BIT_WORD_USHR] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `i < N ==> (N - 1 - i + n < N <=> n <= i)`] THEN
  ASM_CASES_TAC `n:num <= i` THEN ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let WORD_USHR_AS_SHL = prove
 (`!(x:N word) n.
        word_ushr x n =
        word_reversefields 1 (word_shl (word_reversefields 1 x) n)`,
  REWRITE_TAC[WORD_SHL_AS_USHR; WORD_REVERSEFIELDS_REVERSEFIELDS]);;

let WORD_CTZ_SHL = prove
 (`!(x:N word) n.
        word_ctz (word_shl x n) = MIN (dimindex(:N)) (word_ctz x + n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM WORD_CLZ_REVERSEFIELDS; WORD_SHL_AS_USHR;
              WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_CLZ_USHR]);;

(* ------------------------------------------------------------------------- *)
(* Byte reversal, with type constrained to multiple of 8.                    *)
(* ------------------------------------------------------------------------- *)

let word_bytereverse = new_definition
 `(word_bytereverse
    :((((N)tybit0)tybit0)tybit0)word->((((N)tybit0)tybit0)tybit0)word) x =
  word_of_bits { i | i < 8 * dimindex(:N) /\
                     bit (8 * (dimindex(:N) - 1 - i DIV 8) + i MOD 8) x}`;;

let BIT_WORD_BYTEREVERSE = prove
 (`!(x:((((N)tybit0)tybit0)tybit0)word) i.
        bit i (word_bytereverse x) <=>
        i < 8 * dimindex(:N) /\
        bit (8 * (dimindex(:N) - 1 - i DIV 8) + i MOD 8) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_bytereverse; BIT_WORD_OF_BITS] THEN
  REWRITE_TAC[DIMINDEX_TYBIT0; ARITH_RULE `2 * 2 * 2 * n = 8 * n`] THEN
  SET_TAC[]);;

let WORD_BYTEREVERSE_BYTEREVERSE = prove
 (`!(x:((((N)tybit0)tybit0)tybit0)word).
        word_bytereverse(word_bytereverse x) = x`,
  ONCE_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[BIT_WORD_BYTEREVERSE] THEN
  REWRITE_TAC[DIMINDEX_TYBIT0; ARITH_RULE `2 * 2 * 2 * n = 8 * n`] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[ARITH_RULE
   `i < 8 * n ==> 8 * (n - 1 - i DIV 8) + i MOD 8 < 8 * n`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[MOD_MULT_ADD; MOD_MOD_REFL; DIV_MULT_ADD; ARITH_EQ] THEN
  SIMP_TAC[DIV_LT; MOD_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC);;

let WORD_BYTEREVERSE_REVERSEFIELDS = prove
 (`word_bytereverse = word_reversefields 8`,
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[BIT_WORD_BYTEREVERSE; BIT_WORD_REVERSEFIELDS] THEN
  REWRITE_TAC[DIMINDEX_TYBIT0; MULT_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[DIV_MULT; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Multiplication of binary polynomials as words, "carryless multiplication" *)
(* ------------------------------------------------------------------------- *)

let word_pmul = define
 `(word_pmul:M word->N word->P word) x y =
  word_of_bits {k | ODD(CARD {i | i <= k /\ bit i x /\ bit (k - i) y})}`;;

let BIT_WORD_PMUL_ALT = prove
 (`!x y k. bit k ((word_pmul:M word->N word->P word) x y) <=>
           k < dimindex(:P) /\
           ODD(CARD {i | i <= k /\ bit i x /\ bit (k - i) y})`,
  REWRITE_TAC[word_pmul; BIT_WORD_OF_BITS; IN_ELIM_THM]);;

let BIT_WORD_PMUL = prove
 (`!x y k. bit k ((word_pmul:M word->N word->P word) x y) <=>
           k < dimindex(:P) /\
           ODD(nsum (0..k) (\i. bitval(bit i x) * bitval(bit (k - i) y)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIT_WORD_PMUL_ALT] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM BITVAL_AND] THEN
  REWRITE_TAC[bitval; GSYM NSUM_RESTRICT_SET] THEN
  SIMP_TAC[NSUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG] THEN
  REWRITE_TAC[MULT_CLAUSES; LE_0; IN_NUMSEG]);;

let BITVAL_BIT_WORD_PMUL = prove
 (`!x y k. bitval(bit k ((word_pmul:M word->N word->P word) x y)) =
           if k < dimindex(:P)
           then nsum(0..k) (\i. bitval(bit i x) * bitval(bit (k - i) y)) MOD 2
           else 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIT_WORD_PMUL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; BITVAL_ODD]);;

let WORD_PMUL_0 = prove
 (`(!y. (word_pmul:M word->N word->P word) (word 0) y = word 0) /\
   (!x. (word_pmul:M word->N word->P word) x (word 0) = word 0)`,
  REWRITE_TAC[word_pmul; BIT_WORD_0; MULT_CLAUSES; EMPTY_GSPEC;
              CARD_CLAUSES; ODD; WORD_OF_BITS_EMPTY]);;

let WORD_PMUL_XOR = prove
 (`(!x y z. (word_pmul:M word->N word->P word) (word_xor x y) z =
            word_xor (word_pmul x z) (word_pmul y z)) /\
   (!x y z. (word_pmul:M word->N word->P word) x (word_xor y z) =
            word_xor (word_pmul x y) (word_pmul x z))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[BIT_WORD_PMUL; BIT_WORD_XOR_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[GSYM ODD_ADD] THEN
  REWRITE_TAC[MESON[ODD_ADD; NOT_ODD] `(ODD x <=> ODD y) <=> EVEN(x + y)`] THEN
  REWRITE_TAC[GSYM NSUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC(ISPEC `EVEN` NSUM_CLOSED) THEN
  SIMP_TAC[EVEN; EVEN_ADD] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_NUMSEG; LE_0; BITVAL_XOR] THEN
  REWRITE_TAC[bitval] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let WORD_PMUL_ZX = prove
 (`(!x y. word_pmul (word_zx x:P word) y =
          (word_pmul:M word->N word->P word) x y) /\
   (!x y. word_pmul x (word_zx y:P word) =
          (word_pmul:M word->N word->P word) x y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_pmul; BIT_WORD_ZX] THEN
  GEN_REWRITE_TAC I [WORD_OF_BITS_EQ] THEN SIMP_TAC[IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN GEN_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let WORD_PMUL_STEP = prove
 (`!x y. (word_pmul:M word->N word->N word) x y =
         word_xor (if bit 0 x then y else word 0)
                  (word_pmul (word_ushr x 1) (word_shl y 1))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[BIT_WORD_XOR; BIT_WORD_PMUL] THEN
  REWRITE_TAC[TAUT `(p <=> ~(q <=> r)) <=> ~(p <=> r) <=> q`] THEN
  REWRITE_TAC[GSYM ODD_ADD] THEN
  REWRITE_TAC[BIT_WORD_USHR; BIT_WORD_SHL] THEN
  ASM_SIMP_TAC[ARITH_RULE `i:num < N ==> i - j < N`] THEN
  REWRITE_TAC[ARITH_RULE `i - j - 1 = i - (j + 1)`] THEN
  REWRITE_TAC[ARITH_RULE `1 <= i - j <=> j + 1 <= i`] THEN
  REWRITE_TAC[GSYM(SPEC `1` NSUM_OFFSET)] THEN
  SIMP_TAC[NSUM_CLAUSES_LEFT; LE_0] THEN REWRITE_TAC[ADD_CLAUSES] THEN
  REWRITE_TAC[GSYM ADD1; NSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  SIMP_TAC[ARITH_RULE `~(SUC i <= i)`; BITVAL_CLAUSES; MULT_CLAUSES] THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `(i + j) + j = 2 * j + i`] THEN
  REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH_ODD; SUB_0] THEN
  REWRITE_TAC[bitval] THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[BIT_WORD_0] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_PMUL_SYM = prove
 (`!x y. (word_pmul:M word->M word->N word) x y = word_pmul y x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[BIT_WORD_PMUL] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [NSUM_REFLECT] THEN
  ASM_SIMP_TAC[LT; SUB_0; ARITH_RULE `j:num <= i ==> i - (i - j) = j`] THEN
  REWRITE_TAC[MULT_SYM]);;

let WORD_PMUL_POW2 = prove
 (`(!(x:N word) n. word_pmul (word(2 EXP n):N word) x = word_shl x n) /\
   (!(x:N word) n. word_pmul x (word(2 EXP n):N word) = word_shl x n)`,
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [WORD_PMUL_SYM] THEN
  REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[BIT_WORD_PMUL; BIT_WORD_SHL; BIT_WORD_POW2] THEN
  REWRITE_TAC[GSYM BITVAL_AND] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; bitval] THEN
  ONCE_REWRITE_TAC[MESON[]
   `(if p /\ q then 1 else 0) = if p then (if q then 1 else 0) else 0`] THEN
  SIMP_TAC[NSUM_DELTA; IN_NUMSEG; LE_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ODD] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[ARITH_ODD; TAUT `(if x then T else F) <=> x`] THEN
  MATCH_MP_TAC(TAUT `p ==> (p /\ q <=> q)`) THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Alignment. The definition rolls in the assumption that the value is a     *)
(* power of 2 no more than the wordsize, which seems intuitively natural.    *)
(* ------------------------------------------------------------------------- *)

let aligned = new_definition
 `aligned n (a:N word) <=>
    n divides 2 EXP dimindex(:N) /\ n divides val a`;;

let ALIGNED = prove
 (`!n x:N word.
        aligned n x <=>
        n divides 2 EXP dimindex(:N) /\ &n divides ival(x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[aligned] THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)`) THEN
  REWRITE_TAC[num_divides; GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(y:int == x) (mod m)
    ==> n divides m
        ==> (n divides x <=> n divides y)`) THEN
  REWRITE_TAC[IVAL_VAL_CONG]);;

let ALIGNED_WORD = prove
 (`!n k. aligned n (word k:N word) <=>
         n divides 2 EXP dimindex(:N) /\ n divides k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[aligned] THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)`) THEN
  GEN_REWRITE_TAC LAND_CONV [divides] THEN
  REWRITE_TAC[aligned; VAL_WORD; DIVIDES_MOD] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN REWRITE_TAC[MOD_MOD]);;

let ALIGNED_IWORD = prove
 (`!n k. aligned n (iword k:N word) <=>
         n divides 2 EXP dimindex(:N) /\ &n divides k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALIGNED] THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)`) THEN
  REWRITE_TAC[num_divides; GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(x:int == y) (mod m)
    ==> n divides m
        ==> (n divides x <=> n divides y)`) THEN
  REWRITE_TAC[IVAL_IWORD_CONG]);;

let ALIGNED_WORD_0 = prove
 (`!n. aligned n (word 0:N word) <=> n divides 2 EXP dimindex(:N)`,
  REWRITE_TAC[ALIGNED_WORD; VAL_WORD_0] THEN CONV_TAC NUMBER_RULE);;

let ALIGNED_WORD_NEG = prove
 (`!n x:N word. aligned n (word_neg x) <=> aligned n x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALIGNED] THEN
  REWRITE_TAC[num_divides; GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(y:int == --x) (mod e)
    ==> (n divides e /\ n divides y <=> n divides e /\ n divides x)`) THEN
  REWRITE_TAC[ICONG_WORD_NEG]);;

let ALIGNED_WORD_ADD = prove
 (`!n a b:N word.
        aligned n a /\ aligned n b ==> aligned n (word_add a b)`,
  REWRITE_TAC[FORALL_WORD; ALIGNED_WORD; GSYM WORD_ADD] THEN
  CONV_TAC NUMBER_RULE);;

let ALIGNED_WORD_MUL = prove
 (`!n a b:N word.
        aligned n a \/ aligned n b ==> aligned n (word_mul a b)`,
  REWRITE_TAC[FORALL_WORD; ALIGNED_WORD; GSYM WORD_MUL] THEN
  CONV_TAC NUMBER_RULE);;

let ALIGNED_WORD_SUB = prove
 (`!n a b:N word.
        aligned n a /\ aligned n b ==> aligned n (word_sub a b)`,
  REWRITE_TAC[WORD_RULE `word_sub x y:N word = word_add x (word_neg y)`] THEN
  SIMP_TAC[ALIGNED_WORD_NEG; ALIGNED_WORD_ADD]);;

let ALIGNED_WORD_ADD_EQ = prove
 (`(!n x y:N word.
        aligned n x ==> (aligned n (word_add x y) <=> aligned n y)) /\
   (!n x y:N word.
        aligned n y ==> (aligned n (word_add x y) <=> aligned n x))`,
  MESON_TAC[ALIGNED_WORD_ADD; ALIGNED_WORD_NEG; WORD_ADD_SYM;
            WORD_RULE `word_add (word_neg x) (word_add x y) = y`]);;

let ALIGNED_WORD_SUB_EQ = prove
 (`(!n x y:N word.
        aligned n x ==> (aligned n (word_sub x y) <=> aligned n y)) /\
   (!n x y:N word.
        aligned n y ==> (aligned n (word_sub x y) <=> aligned n x))`,
  REWRITE_TAC[WORD_RULE `word_sub x y = word_add x (word_neg y)`] THEN
  MESON_TAC[ALIGNED_WORD_ADD_EQ; ALIGNED_WORD_NEG]);;

(* ------------------------------------------------------------------------- *)
(* JVM-specific word operations, though they may well work in other places.  *)
(*                                                                           *)
(* All shift operations mask out the lower bits as the unsigned shift count. *)
(*                                                                           *)
(* Division does truncation towards zero; at this level there is no concept  *)
(* of an exception on division by zero. Note that the JVM is defined anyway  *)
(* so INT_MIN / -1 doesn't generate any exception, just returning the        *)
(* correct modular result as per the usual pattern.                          *)
(*                                                                           *)
(* Remainder is then defined by the usual Euclidean identity.                *)
(* ------------------------------------------------------------------------- *)

let word_jshl = new_definition
 `word_jshl (x:N word) (y:N word) =
        word_shl x (val y MOD dimindex(:N))`;;

let word_jshr = new_definition
 `word_jshr (x:N word) (y:N word) =
        word_ishr x (val y MOD dimindex(:N))`;;

let word_jushr = new_definition
 `word_jushr (x:N word) (y:N word) =
        word_ushr x (val y MOD dimindex(:N))`;;

let word_jdiv = new_definition
 `word_jdiv:N word->N word->N word =
   imodular (\a b. int_sgn a * int_sgn b * (abs(a) div abs(b)))`;;

let word_jrem = new_definition
 `word_jrem (x:N word) (y:N word) =
    word_sub x (word_mul (word_jdiv x y) y)`;;

(* ------------------------------------------------------------------------- *)
(* The JVM doesn't include rotates as primitive, but here is what they       *)
(* obviously would be like, and proof that some emulations work. Note that   *)
(* emulation using negative shifts relies not only on the Java               *)
(* masking treatment of shift counts but also on the word size being a       *)
(* power of 2 (of course for the JVM it is 2^5 = 32 or 2^6 = 64).            *)
(* ------------------------------------------------------------------------- *)

let word_jror = new_definition
 `word_jror (w:N word) (k:N word) = word_ror w (val k)`;;

let word_jrol = new_definition
 `word_jrol (w:N word) (k:N word) = word_rol w (val k)`;;

let VAL_WORD_NEG_MOD_DIMINDEX = prove
 (`!k:N word.
        dimindex(:N) divides 2 EXP dimindex(:N)
        ==> (val(word_neg k) == dimindex (:N) - val k MOD dimindex(:N))
            (mod dimindex(:N))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_NEG; CONG] THEN
  MATCH_MP_TAC(MESON[]
   `x MOD n MOD m = x MOD m /\ x MOD m = y ==> x MOD n MOD m = y`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[divides; MOD_MOD]; ALL_TAC] THEN
  REWRITE_TAC[GSYM CONG; num_congruent] THEN
  SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE; VAL_BOUND; DIVISION;
           DIMINDEX_NONZERO; GSYM INT_OF_NUM_REM] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `n divides e /\ (k':int == k) (mod n) ==> (e - k == n - k') (mod n)`) THEN
  ASM_REWRITE_TAC[GSYM num_divides; INT_REM_MOD_SELF]);;

let WORD_JROL_JROR = prove
 (`!w k:N word.
        dimindex(:N) divides 2 EXP dimindex(:N)
        ==> word_jrol w k = word_jror w (word_neg k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_jrol; word_jror] THEN
  REWRITE_TAC[WORD_ROL_ROR_GEN] THEN MATCH_MP_TAC WORD_ROR_PERIODIC THEN
  ONCE_REWRITE_TAC[NUMBER_RULE
   `(x:num == y) (mod n) <=> (y == x) (mod n)`] THEN
  MATCH_MP_TAC VAL_WORD_NEG_MOD_DIMINDEX THEN ASM_REWRITE_TAC[]);;

let WORD_JROR_JROL = prove
 (`!w k:N word.
        dimindex(:N) divides 2 EXP dimindex(:N)
        ==> word_jror w k = word_jrol w (word_neg k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_jrol; word_jror] THEN
  REWRITE_TAC[WORD_ROR_ROL_GEN] THEN MATCH_MP_TAC WORD_ROL_PERIODIC THEN
  ONCE_REWRITE_TAC[NUMBER_RULE
   `(x:num == y) (mod n) <=> (y == x) (mod n)`] THEN
  MATCH_MP_TAC VAL_WORD_NEG_MOD_DIMINDEX THEN ASM_REWRITE_TAC[]);;

let WORD_JROR = prove
 (`!w k:N word.
        dimindex(:N) divides 2 EXP dimindex(:N)
        ==> word_jror w k =
            word_or (word_jushr w k) (word_jshl w (word_neg k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_jror; word_jushr; word_jshl] THEN
  ONCE_REWRITE_TAC[WORD_ROR_MOD] THEN
  SIMP_TAC[WORD_ROR_SHIFTS; DIVISION; DIMINDEX_NONZERO; LT_IMP_LE] THEN
  FIRST_X_ASSUM(MP_TAC o ISPEC `k:N word` o
    MATCH_MP VAL_WORD_NEG_MOD_DIMINDEX) THEN
  REWRITE_TAC[CONG] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `val(k:N word) MOD dimindex(:N) = 0` THENL
   [ASM_REWRITE_TAC[SUB_0; MOD_REFL; WORD_USHR_ZERO; WORD_SHL_ZERO] THEN
    MATCH_MP_TAC(WORD_BITWISE_RULE
     `y = word 0 ==> word_or x y = word_or x x`) THEN
    REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_SHL; MOD_MULT];
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[ARITH_RULE `n - k < n <=> ~(k = 0) /\ ~(n = 0)`] THEN
    ASM_REWRITE_TAC[DIMINDEX_NONZERO]]);;

let WORD_JROL = prove
 (`!w k:N word.
        dimindex(:N) divides 2 EXP dimindex(:N)
        ==> word_jrol w k =
            word_or (word_jshl w k) (word_jushr w (word_neg k))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WORD_JROL_JROR; WORD_JROR] THEN
  ONCE_REWRITE_TAC[WORD_RULE `word_neg(word_neg x):N word = x`] THEN
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_JUSHR_NEG = prove
 (`!w k:N word.
        dimindex(:N) divides 2 EXP dimindex(:N)
        ==> word_jushr w (word_neg k) =
            if val k MOD dimindex(:N) = 0 then w
            else word_ushr w (dimindex(:N) - val k MOD dimindex(:N))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_jushr] THEN
  ASM_SIMP_TAC[REWRITE_RULE[CONG] VAL_WORD_NEG_MOD_DIMINDEX] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[SUB_0; MOD_REFL; WORD_USHR_ZERO] THEN
  ASM_SIMP_TAC[MOD_LT; DIMINDEX_GE_1; ARITH_RULE
    `1 <= n /\ ~(m = 0) ==> n - m < n`]);;

let WORD_JSHL_NEG = prove
 (`!w k:N word.
        dimindex(:N) divides 2 EXP dimindex(:N)
        ==> word_jshl w (word_neg k) =
            if val k MOD dimindex(:N) = 0 then w
            else word_shl w (dimindex(:N) - val k MOD dimindex(:N))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_jshl] THEN
  ASM_SIMP_TAC[REWRITE_RULE[CONG] VAL_WORD_NEG_MOD_DIMINDEX] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[SUB_0; MOD_REFL; WORD_SHL_ZERO] THEN
  ASM_SIMP_TAC[MOD_LT; DIMINDEX_GE_1; ARITH_RULE
    `1 <= n /\ ~(m = 0) ==> n - m < n`]);;

(* ------------------------------------------------------------------------- *)
(* Conversion for "j" forms applied to numeral shift/rotate word.            *)
(* ------------------------------------------------------------------------- *)

let WORD_WORD_OPERATION_CONV =
  let pth = prove
   (`word_jshl (x:N word) (word n) =
     word_shl x (n MOD (2 EXP dimindex(:N)) MOD dimindex(:N)) /\
     word_jshr x (word n) =
     word_ishr x (n MOD (2 EXP dimindex(:N)) MOD dimindex(:N)) /\
     word_jushr x (word n) =
     word_ushr x (n MOD (2 EXP dimindex(:N)) MOD dimindex(:N)) /\
     word_jrol x (word n) =
     word_rol x (n MOD (2 EXP dimindex(:N)) MOD dimindex(:N)) /\
     word_jror x (word n) =
     word_ror x (n MOD (2 EXP dimindex(:N)) MOD dimindex(:N))`,
    REWRITE_TAC[word_jshl; word_jshr; word_jushr; word_jrol; word_jror] THEN
    REWRITE_TAC[VAL_WORD; GSYM WORD_ROL_MOD; GSYM WORD_ROR_MOD]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV
   (BINOP2_CONV (RAND_CONV (!word_POW2SIZE_CONV) THENC NUM_MOD_CONV)
                (!word_SIZE_CONV) THENC
    NUM_MOD_CONV);;

(* ------------------------------------------------------------------------- *)
(* Emulation of unsigned comparisons using signed (useful for the JVM).      *)
(* ------------------------------------------------------------------------- *)

let IVAL_TOPFLIP_VAL = prove
 (`!w:N word.
        ival(word_xor word_INT_MIN w) =
        &(val w) - &2 pow (dimindex(:N) - 1)`,
  REWRITE_TAC[INT_IVAL; WORD_XOR_INT_MIN] THEN
  REWRITE_TAC[INT_VAL_WORD_ADD_CASES; INT_VAL_WORD_INT_MIN; MSB_INT_VAL] THEN
  WORD_ARITH_TAC);;

let WORD_ULE_TOPFLIP = prove
 (`!v w:N word.
        word_ule v w <=>
        word_ile (word_xor (word_INT_MIN) v) (word_xor (word_INT_MIN) w)`,
  REWRITE_TAC[word_ule; word_ile; relational2; irelational2] THEN
  REWRITE_TAC[IVAL_TOPFLIP_VAL; GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;

let WORD_ULT_TOPFLIP = prove
 (`!v w:N word.
        word_ult v w <=>
        word_ilt (word_xor (word_INT_MIN) v) (word_xor (word_INT_MIN) w)`,
  REWRITE_TAC[word_ult; word_ilt; relational2; irelational2] THEN
  REWRITE_TAC[IVAL_TOPFLIP_VAL; GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

let WORD_UGE_TOPFLIP = prove
 (`!v w:N word.
        word_uge v w <=>
        word_ige (word_xor (word_INT_MIN) v) (word_xor (word_INT_MIN) w)`,
  REWRITE_TAC[word_uge; word_ige; relational2; irelational2] THEN
  REWRITE_TAC[IVAL_TOPFLIP_VAL; INT_GE; GE; GSYM INT_OF_NUM_LE] THEN
  INT_ARITH_TAC);;

let WORD_UGT_TOPFLIP = prove
 (`!v w:N word.
        word_ugt v w <=>
        word_igt (word_xor (word_INT_MIN) v) (word_xor (word_INT_MIN) w)`,
  REWRITE_TAC[word_ugt; word_igt; relational2; irelational2] THEN
  REWRITE_TAC[IVAL_TOPFLIP_VAL; INT_GT; GT; GSYM INT_OF_NUM_LT] THEN
  INT_ARITH_TAC);;

let WORD_ILT_TOPFLIP = prove
 (`!v w:N word.
        word_ilt v w <=>
        word_ult (word_xor word_INT_MIN v) (word_xor word_INT_MIN w)`,
  REWRITE_TAC[WORD_ULT_TOPFLIP] THEN
  REWRITE_TAC[WORD_BITWISE_RULE `word_xor m (word_xor m x) = x`]);;

let WORD_ILE_TOPFLIP = prove
 (`!v w:N word.
        word_ile v w <=>
        word_ule (word_xor word_INT_MIN v) (word_xor word_INT_MIN w)`,
  REWRITE_TAC[WORD_ULE_TOPFLIP] THEN
  REWRITE_TAC[WORD_BITWISE_RULE `word_xor m (word_xor m x) = x`]);;

let WORD_IGT_TOPFLIP = prove
 (`!v w:N word.
        word_igt v w <=>
        word_ugt (word_xor word_INT_MIN v) (word_xor word_INT_MIN w)`,
  REWRITE_TAC[WORD_UGT_TOPFLIP] THEN
  REWRITE_TAC[WORD_BITWISE_RULE `word_xor m (word_xor m x) = x`]);;

let WORD_IGE_TOPFLIP = prove
 (`!v w:N word.
        word_ige v w <=>
        word_uge (word_xor word_INT_MIN v) (word_xor word_INT_MIN w)`,
  REWRITE_TAC[WORD_UGE_TOPFLIP] THEN
  REWRITE_TAC[WORD_BITWISE_RULE `word_xor m (word_xor m x) = x`]);;

(* ------------------------------------------------------------------------- *)
(* Characterizing exactness of word add or add-with-carry via comparison.    *)
(* ------------------------------------------------------------------------- *)

let WORD_LE_ADD_EXACT = prove
 (`(!x y:N word.
        val x <= val(word_add x y) <=> val(word_add x y) = val x + val y) /\
   (!x y:N word.
        val y <= val(word_add x y) <=> val(word_add x y) = val x + val y)`,
  WORD_ARITH_TAC);;

let WORD_ADD_LT_EXACT = prove
 (`(!x y:N word.
        val(word_add x y) < val x <=>
        val(word_add x y) + 2 EXP dimindex(:N) = val x + val y) /\
   (!x y:N word.
        val(word_add x y) < val y <=>
        val(word_add x y) + 2 EXP dimindex(:N) = val x + val y)`,
  WORD_ARITH_TAC);;

let WORD_ADD_LT_INEXACT = prove
 (`(!x y:N word.
        val(word_add x y) < val x <=> ~(val(word_add x y) = val x + val y)) /\
   (!x y:N word.
        val(word_add x y) < val y <=> ~(val(word_add x y) = val x + val y))`,
  WORD_ARITH_TAC);;

let WORD_LT_ADC_EXACT = prove
 (`(!x y:N word.
        val x < val(word_add (word_add x y) (word 1)) <=>
        val(word_add (word_add x y) (word 1)) = val x + val y + 1) /\
  (!x y:N word.
        val y < val(word_add (word_add x y) (word 1)) <=>
        val(word_add (word_add x y) (word 1)) = val x + val y + 1)`,
  WORD_ARITH_TAC);;

let WORD_ADC_LE_EXACT = prove
 (`(!x y:N word.
        val(word_add (word_add x y) (word 1)) <= val x <=>
        val(word_add (word_add x y) (word 1)) + 2 EXP dimindex(:N) =
        val x + val y + 1) /\
  (!x y:N word.
        val(word_add (word_add x y) (word 1)) <= val y <=>
        val(word_add (word_add x y) (word 1)) + 2 EXP dimindex(:N) =
        val x + val y + 1)`,
  WORD_ARITH_TAC);;

let WORD_ADC_LE_INEXACT = prove
 (`(!x y:N word.
        val(word_add (word_add x y) (word 1)) <= val x <=>
        ~(val(word_add (word_add x y) (word 1)) = val x + val y + 1)) /\
  (!x y:N word.
        val(word_add (word_add x y) (word 1)) <= val y <=>
        ~(val(word_add (word_add x y) (word 1)) = val x + val y + 1))`,
  WORD_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Conversion for explicit numeric bits of word operations, one level.       *)
(* For example BIT_WORD_CONV `bit 7 (word_sub x y:int16)`                    *)
(* ------------------------------------------------------------------------- *)

let BIT_WORD_CONV =
  let pth_ror = prove
   (`bit i (word_ror (w:N word) n) <=>
          (\m. (\s. if s < dimindex(:N) then bit s w
                    else i < dimindex(:N) /\ bit (s - dimindex(:N)) w)
               (i + m))
          (n MOD dimindex(:N))`,
    REWRITE_TAC[BIT_WORD_ROR])
  and pth_rol = prove
   (`bit i (word_rol (w:N word) n) <=>
          (\m. if i < m then bit (i + dimindex(:N) - m) w
               else i < dimindex(:N) /\ bit (i - m) w)
          (n MOD dimindex(:N))`,
    REWRITE_TAC[BIT_WORD_ROL]) in
  let rule_add = (MATCH_MP o prove)
   (`n = SUC m
     ==> (bit n (word_add x y:N word) <=>
          n < dimindex(:N) /\
          ((bit n x <=> bit n y) <=>
           bit m x /\ bit m y \/
           (bit m x \/ bit m y) /\ ~bit m (word_add x y)))`,
    SIMP_TAC[REWRITE_RULE[GSYM ADD1] BIT_WORD_ADD_CLAUSES])
  and rule_sub = (MATCH_MP o prove)
   (`n = SUC m
     ==> (bit n (word_sub x y:N word) <=>
          n < dimindex(:N) /\
          ((bit n x <=> bit n y) <=>
           ~bit m x /\ bit m y \/
           (~bit m x \/ bit m y) /\ bit m (word_sub x y)))`,
    SIMP_TAC[REWRITE_RULE[GSYM ADD1] BIT_WORD_SUB_CLAUSES])
  and rule_neg = (MATCH_MP o prove)
   (`n = SUC m
     ==> (bit n (word_neg x:N word) <=>
          n < dimindex(:N) /\
          (bit n x <=> ~bit m x /\ ~bit m (word_neg x)))`,
    SIMP_TAC[REWRITE_RULE[GSYM ADD1] BIT_WORD_NEG_CLAUSES])
  and conv_shl = GEN_REWRITE_CONV I [REWRITE_RULE[CONJ_ASSOC] BIT_WORD_SHL]
  and conv_ror = GEN_REWRITE_CONV I [pth_ror]
  and conv_rol = GEN_REWRITE_CONV I [pth_rol]
  and conv_cond_t = GEN_REWRITE_CONV I [CONJUNCT1(SPEC_ALL COND_CLAUSES)]
  and conv_cond_f = GEN_REWRITE_CONV I [CONJUNCT2(SPEC_ALL COND_CLAUSES)]
  and conv_and = GEN_REWRITE_CONV I [AND_CLAUSES]
  and conv_and_t = GEN_REWRITE_CONV I [CONJUNCT1(SPEC_ALL AND_CLAUSES)]
  and conv_and_f = GEN_REWRITE_CONV I [el 2 (CONJUNCTS(SPEC_ALL AND_CLAUSES))]
  and zero_tm = `0` and one_tm = `1` in
  fun tm ->
    match tm with
      Comb(Comb(Const("bit",_),n),
           Comb(Const("word",_),Comb(Const("bitval",_),_)))
      when is_numeral n ->
        (GEN_REWRITE_CONV I [BIT_WORD_BITVAL] THENC
         LAND_CONV NUM_EQ_CONV THENC conv_and) tm
    | Comb(Comb(Const("bit",_),n),Comb(Const("word",_),m))
      when is_numeral n && is_numeral m ->
          if m = zero_tm then
            GEN_REWRITE_CONV I [BIT_WORD_0] tm
          else if m = one_tm then
            (GEN_REWRITE_CONV I [BIT_WORD_1] THENC NUM_EQ_CONV) tm
          else
            (GEN_REWRITE_CONV I [BIT_WORD] THENC
             BINOP2_CONV (RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV)
                         (RAND_CONV (RAND_CONV NUM_EXP_CONV THENC
                                     NUM_DIV_CONV) THENC
                          NUM_ODD_CONV) THENC
             conv_and) tm
    | Comb(Comb(Const("bit",_),n),Comb(Const("word",_),m))
      when is_numeral n && m = one_tm ->
          (GEN_REWRITE_CONV I [BIT_WORD_1] THENC NUM_EQ_CONV) tm
    | Comb(Comb(Const("bit",_),n),Comb(Const("word_not",_),_))
      when is_numeral n ->
       (GEN_REWRITE_CONV I [BIT_WORD_NOT] THENC
        LAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV) THENC
        conv_and) tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_and",_),_),_))
      when is_numeral n ->
        GEN_REWRITE_CONV I [BIT_WORD_AND_ALT] tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_or",_),_),_))
      when is_numeral n ->
        GEN_REWRITE_CONV I [BIT_WORD_OR_ALT] tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_xor",_),_),_))
      when is_numeral n ->
        GEN_REWRITE_CONV I [BIT_WORD_XOR_ALT] tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_add",_),_),_))
      when is_numeral n ->
        if n = zero_tm then
         (GEN_REWRITE_CONV I [CONJUNCT1 BIT_WORD_ADD_CLAUSES]) tm
        else
         (GEN_REWRITE_CONV I [rule_add (num_CONV n)] THENC
          LAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV) THENC
          conv_and) tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_sub",_),_),_))
      when is_numeral n ->
        if n = zero_tm then
         (GEN_REWRITE_CONV I [CONJUNCT1 BIT_WORD_SUB_CLAUSES]) tm
        else
         (GEN_REWRITE_CONV I [rule_sub (num_CONV n)] THENC
          LAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV) THENC
          conv_and) tm
    | Comb(Comb(Const("bit",_),n),
           Comb(Const("word_neg",_),
                 Comb(Const("word",_),Comb(Const("bitval",_),_))))
      when is_numeral n ->
        (GEN_REWRITE_CONV I [BIT_WORD_MASK] THENC
         LAND_CONV (RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV) THENC
         conv_and) tm
    | Comb(Comb(Const("bit",_),n),Comb(Const("word_neg",_),_))
      when is_numeral n ->
        if n = zero_tm then
         (GEN_REWRITE_CONV I [CONJUNCT1 BIT_WORD_NEG_CLAUSES]) tm
        else
         (GEN_REWRITE_CONV I [rule_neg (num_CONV n)] THENC
          LAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV) THENC
          conv_and) tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_shl",_),_),m))
      when is_numeral n && is_numeral m ->
        (conv_shl THENC
         BINOP2_CONV (BINOP2_CONV NUM_LE_CONV
                       (RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV) THENC
                         conv_and)
                     (LAND_CONV NUM_SUB_CONV) THENC
         conv_and) tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_ushr",_),_),m))
      when is_numeral n && is_numeral m ->
        (GEN_REWRITE_CONV I [BIT_WORD_USHR] THENC LAND_CONV NUM_ADD_CONV) tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_ishr",_),_),m))
      when is_numeral n && is_numeral m ->
        (GEN_REWRITE_CONV I [BIT_WORD_ISHR] THENC
         RATOR_CONV(LAND_CONV
           (BINOP2_CONV NUM_ADD_CONV (!word_SIZE_CONV) THENC
            NUM_LT_CONV)) THENC
         ((conv_cond_t THENC
           LAND_CONV NUM_ADD_CONV) ORELSEC
          (conv_cond_f THENC
           COMB2_CONV
              (RAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV))
              (LAND_CONV(LAND_CONV(!word_SIZE_CONV) THENC NUM_SUB_CONV)) THENC
           conv_and))) tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_ror",_),_),m))
      when is_numeral n && is_numeral m ->
        (conv_ror THENC
         RAND_CONV (RAND_CONV(!word_SIZE_CONV) THENC NUM_MOD_CONV) THENC
         BETA_CONV THENC RAND_CONV NUM_ADD_CONV THENC BETA_CONV THENC
         RATOR_CONV(LAND_CONV
          (RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV)) THENC
         (conv_cond_t ORELSEC
          (conv_cond_f THENC
           LAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV) THENC
           ((conv_and_t THENC
             LAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_SUB_CONV)) ORELSEC
            conv_and_f
           ))))
        tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_rol",_),_),m))
      when is_numeral n && is_numeral m ->
        (conv_rol THENC
         RAND_CONV (RAND_CONV(!word_SIZE_CONV) THENC NUM_MOD_CONV) THENC
         BETA_CONV THENC
         RATOR_CONV(LAND_CONV NUM_LT_CONV) THENC
         ((conv_cond_t THENC
           LAND_CONV(RAND_CONV
            (LAND_CONV(!word_SIZE_CONV) THENC NUM_SUB_CONV) THENC
           NUM_ADD_CONV)) ORELSEC
          (conv_cond_f THENC
           LAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV) THENC
           ((conv_and_t THENC
             LAND_CONV NUM_SUB_CONV) ORELSEC
            conv_and_f)
         ))) tm
    | Comb(Comb(Const("bit",_),n),Comb(Const("word_zx",_),_))
      when is_numeral n ->
       (GEN_REWRITE_CONV I [BIT_WORD_ZX] THENC
        LAND_CONV (RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV) THENC
        (conv_and_f ORELSEC conv_and_t)) tm
   | Comb(Comb(Const("bit",_),n),Comb(Const("word_sx",_),_))
      when is_numeral n ->
       (GEN_REWRITE_CONV I [BIT_WORD_SX] THENC
         LAND_CONV (RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV) THENC
         (conv_and_f ORELSEC
          (conv_and_t THENC
           LAND_CONV (RAND_CONV
             (LAND_CONV(!word_SIZE_CONV) THENC NUM_SUB_CONV) THENC
             NUM_MIN_CONV)))) tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_sxfrom",_),i),_))
      when is_numeral n && is_numeral i ->
       (GEN_REWRITE_CONV I [BIT_WORD_SXFROM] THENC
        LAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV) THENC
        (conv_and_f ORELSEC
         (conv_and_t THENC LAND_CONV NUM_MIN_CONV))) tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_join",_),_),_))
      when is_numeral n ->
        (GEN_REWRITE_CONV I [BIT_WORD_JOIN] THENC
         LAND_CONV (RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV) THENC
         (conv_and_f ORELSEC
          (conv_and_t THENC
           RATOR_CONV(LAND_CONV
            (RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV)) THENC
           (conv_cond_t ORELSEC
            (conv_cond_f THENC
             LAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_SUB_CONV))
          )))) tm
    | Comb(Comb(Const("bit",_),n),
           Comb(Comb(Const("word_subword",_),_),
                Comb(Comb(Const(",",_),p),q)))
        when is_numeral n && is_numeral p && is_numeral q ->
         (GEN_REWRITE_CONV I [BIT_WORD_SUBWORD] THENC
          LAND_CONV
           (RAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_MIN_CONV) THENC
            NUM_LT_CONV) THENC
          ((conv_and_t THENC
             LAND_CONV NUM_ADD_CONV) ORELSEC
            conv_and_f)) tm
    | Comb(Comb(Const("bit",_),n),Comb(Const("word_bytereverse",_),_))
      when is_numeral n ->
       (GEN_REWRITE_CONV I [BIT_WORD_BYTEREVERSE] THENC
        BINOP2_CONV (DEPTH_CONV((!word_SIZE_CONV) ORELSEC NUM_RED_CONV))
         (LAND_CONV (DEPTH_CONV((!word_SIZE_CONV) ORELSEC NUM_RED_CONV))) THENC
        (conv_and_t ORELSEC conv_and_f)) tm
    | Comb(Comb(Const("bit",_),n),
           Comb(Comb(Const("word_reversefields",_),b),_))
      when is_numeral n && is_numeral b ->
       (GEN_REWRITE_CONV I [BIT_WORD_REVERSEFIELDS] THENC
        BINOP2_CONV (DEPTH_CONV((!word_SIZE_CONV) ORELSEC NUM_RED_CONV))
         (LAND_CONV (DEPTH_CONV((!word_SIZE_CONV) ORELSEC NUM_RED_CONV))) THENC
        (conv_and_t ORELSEC conv_and_f)) tm
    | Comb(Comb(Const("bit",_),n),
           Comb(Comb(Comb(Const("word_insert",_),x),
                     Comb(Comb(Const(",",_),pos),len)),y))
      when is_numeral n && is_numeral pos && is_numeral len ->
       (GEN_REWRITE_CONV I [BIT_WORD_INSERT] THENC
        LAND_CONV (DEPTH_CONV((!word_SIZE_CONV) ORELSEC NUM_RED_CONV)) THENC
        (conv_and_f ORELSEC
         (conv_and_t THENC
          RATOR_CONV(LAND_CONV(DEPTH_CONV NUM_RED_CONV)) THENC
          (conv_cond_f ORELSEC
           (conv_cond_t THENC LAND_CONV NUM_SUB_CONV))))) tm
    | Comb(Comb(Const("bit",_),n),Comb(Const("word_duplicate",_),x))
      when is_numeral n ->
        (GEN_REWRITE_CONV I [BIT_WORD_DUPLICATE] THENC
         LAND_CONV(RAND_CONV (!word_SIZE_CONV) THENC NUM_LT_CONV) THENC
         (conv_and_f ORELSEC
          (conv_and_t THENC
           LAND_CONV(RAND_CONV (!word_SIZE_CONV) THENC NUM_MOD_CONV)))) tm
    | Comb(Comb(Const("bit",_),n),x) ->
        let th = ISPECL [x;n] BIT_TRIVIAL in
        let tm = lhand(concl th) in
        let ath = (LAND_CONV(!word_SIZE_CONV) THENC NUM_LE_CONV) tm in
        (try MP th (EQT_ELIM ath)
         with Failure _ -> failwith "BIT_WORD_CONV: no change")
    | _ -> failwith "BIT_WORD_CONV: not of expected form";;

(* ------------------------------------------------------------------------- *)
(* A kind of bit-blasting, but with just arithmetic not SAT at the base.     *)
(* ------------------------------------------------------------------------- *)

let WORD_BLAST =
  let pth_lt = prove
   (`~(n = 0) ==> (val x < n <=> val x DIV n = 0)`,
    SIMP_TAC[DIV_EQ_0])
  and pth_le = prove
   (`val x <= n <=> val x DIV (n + 1) = 0`,
    REWRITE_TAC[ARITH_RULE `x <= n <=> x < n + 1`] THEN
    SIMP_TAC[DIV_EQ_0; ADD_EQ_0; ARITH])
  and icong_lemma = INTEGER_RULE
    `(x:int == y) (mod n) <=> (x - y == &0) (mod n)`
  and idiv_lemma = INTEGER_RULE
    `!d. d * n = x ==> (x:int == &0) (mod n)`
  and imon_lemma = INTEGER_RULE
    `(x:int == &0) (mod n) ==> (x * y == &0) (mod n)`
  and ipol_lemma = INTEGER_RULE
    `(x:int == &0) (mod n) /\ (y == &0) (mod n) ==> (x + y == &0) (mod n)` in
  let conv =
    ONCE_DEPTH_CONV VAL_EXPAND_CONV THENC
    TOP_DEPTH_CONV BIT_WORD_CONV THENC
    REWRITE_CONV[BITVAL_CLAUSES] THENC
    REWRITE_CONV[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM] THENC
    REWRITE_CONV[INT_BITVAL_AND; INT_BITVAL_OR; INT_BITVAL_NOT;
                 INT_BITVAL_IMP; INT_BITVAL_IFF] THENC
    ONCE_DEPTH_CONV
     ((GEN_REWRITE_CONV I [GSYM INT_SUB_0] THENC
       LAND_CONV BINT_POLY_CONV) ORELSEC
      (GEN_REWRITE_CONV I [icong_lemma] THENC
       RATOR_CONV(LAND_CONV BINT_POLY_CONV)))
  and conv_lt tm =
    let th = PART_MATCH (lhand o rand) pth_lt tm in
    MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))) in
  let tac_word =
    CONV_TAC WORD_VAL_CONG_CONV THEN
    TRY(CONV_TAC(RAND_CONV(RAND_CONV
     (GEN_REWRITE_CONV I [INT_OF_NUM_POW] THENC
      RAND_CONV(!word_POW2SIZE_CONV))))) THEN
    CONV_TAC conv THEN
    REPEAT
     ((MATCH_MP_TAC idiv_lemma THEN
       W(fun (asl,w) ->
        let l,r = dest_eq(snd(dest_exists w)) in
        EXISTS_TAC (mk_intconst
         (dest_intconst r // dest_intconst(rand l)))) THEN
       CONV_TAC INT_REDUCE_CONV THEN NO_TAC) ORELSE
      (MATCH_MP_TAC ipol_lemma ORELSE MATCH_MP_TAC imon_lemma))
  and tac_num =
    REWRITE_TAC[GSYM VAL_EQ] THEN
    REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[CONG; DIVIDES_MOD; pth_le] THEN
    CONV_TAC(ONCE_DEPTH_CONV conv_lt) THEN
    CONV_TAC conv THEN
    (INT_ARITH_TAC ORELSE CONV_TAC INT_RING) in
  fun tm ->
    try
      prove(tm,REPEAT(GEN_TAC ORELSE CONJ_TAC) THEN
              (tac_word ORELSE tac_num))
    with Failure m ->
      failwith ("WORD_BLAST `" ^ (string_of_term tm) ^ "`: " ^ m);;

(* ------------------------------------------------------------------------- *)
(* Subadditivity (and a bit more) of popcount.                               *)
(* ------------------------------------------------------------------------- *)

let WORD_POPCOUNT_ADD_OR = prove
 (`!x y:N word. word_popcount(word_add x y) <= word_popcount(word_or x y)`,
  REPEAT GEN_TAC THEN ABBREV_TAC
   `word_carryout:N word->N word->N word =
      \x y. word_or (word_and x y)
                    (word_and (word_xor x y) (word_not(word_add x y)))` THEN
  MATCH_MP_TAC(ARITH_RULE
   `!x y:num. x <= y /\ a + y <= b + x ==> a <= b`) THEN
  MAP_EVERY EXISTS_TAC
   [`word_popcount(word_and x y:N word)`;
    `word_popcount(word_carryout (x:N word) (y:N word):N word)`] THEN
  REWRITE_TAC[WORD_POPCOUNT_OR_AND] THEN CONJ_TAC THENL
   [EXPAND_TAC "word_carryout" THEN
    MATCH_MP_TAC WORD_POPCOUNT_LE_BITS THEN
    SIMP_TAC[BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_XOR];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_POPCOUNT_NSUM] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  SIMP_TAC[REAL_OF_NUM_SUM; FINITE_NUMSEG_LT; GSYM SUM_ADD;
           GSYM SUM_LMUL; GSYM SUM_SUB; GSYM REAL_OF_NUM_ADD] THEN
  SUBGOAL_THEN
   `!x (y:N word) i.
      i < dimindex(:N)
      ==> &(bitval(bit i (word_add x y))):real =
          (&(bitval(bit i x)) + &(bitval(bit i y))) +
          ((if i = 0 then &0
            else &(bitval(bit (i - 1) (word_carryout x y:N word)))) -
           &2 * &(bitval(bit i (word_carryout x y))))`
  (fun th -> SIMP_TAC[th]) THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "word_carryout" THEN
    REWRITE_TAC[BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_NOT; BIT_WORD_XOR] THEN
    MP_TAC(ISPECL [`x:N word`; `y:N word`; `i:num`] BIT_WORD_ADD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ADD_SUB; ADD_EQ_0; ARITH_EQ] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < n ==> i - 1 < n`] THEN
    ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`word_add x y:N word`,`z:N word`) THEN CONV_TAC WORD_BLAST;
    REWRITE_TAC[REAL_ARITH
     `(x + y) - (((x + y) + w - &2 * z) + z):real = z - w`]] THEN
  MP_TAC(ISPECL
   [`\i. if i = 0 then &0:real else
         &(bitval(bit (i - 1) (word_carryout (x:N word) (y:N word): N word)))`;
    `0`; `dimindex(:N)-1`] (GEN_ALL SUM_DIFFS_ALT)) THEN
  REWRITE_TAC[ADD_EQ_0; ARITH_EQ; NUMSEG_LT_DIMINDEX; ADD_SUB] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LE_0] THEN REAL_ARITH_TAC);;

let WORD_POPCOUNT_ADD = prove
 (`!x y:N word.
    word_popcount(word_add x y) <= word_popcount x + word_popcount y`,
  MESON_TAC[LE_TRANS; WORD_POPCOUNT_ADD_OR; WORD_POPCOUNT_OR]);;

let WORD_POPCOUNT_MUL = prove
 (`!x y:N word.
        word_popcount(word_mul x y) <= word_popcount x * word_popcount y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_MUL_EXPAND_ALT] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [WORD_POPCOUNT_NSUM] THEN
  SPEC_TAC(`dimindex(:N)`,`n:num`) THEN MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[CONJUNCT1 LT; NSUM_CLAUSES_NUMSEG_LT] THEN
  REWRITE_TAC[WORD_POPCOUNT_0; MULT_CLAUSES; LE_REFL] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[WORD_ADD] THEN
  W(MP_TAC o PART_MATCH lhand WORD_POPCOUNT_ADD o lhand o snd) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LE_TRANS) THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN MATCH_MP_TAC LE_ADD2 THEN
  ASM_REWRITE_TAC[WORD_VAL] THEN REWRITE_TAC[WORD_AND_MASK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; BITVAL_CLAUSES] THEN
  REWRITE_TAC[WORD_POPCOUNT_0; LE_REFL; WORD_POPCOUNT_SHL]);;

let WORD_ODDPARITY_POPCOUNT = prove
 (`!x:N word. word(bitval(word_oddparity x)):M word =
              word_zx(word(word_popcount x):1 word)`,
  GEN_TAC THEN REWRITE_TAC[word_oddparity] THEN
  ONCE_REWRITE_TAC[WORD_BLAST `x:1 word = word(bitval(bit 0 x))`] THEN
  REWRITE_TAC[WORD_ZX_BITVAL; BIT_LSB_WORD]);;

let WORD_EVENPARITY_POPCOUNT = prove
 (`!x:N word. word(bitval(word_evenparity x)):M word =
              word_zx(word_not(word(word_popcount x)):1 word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_evenparity; GSYM NOT_ODD] THEN
  ONCE_REWRITE_TAC[WORD_BLAST `x:1 word = word(bitval(bit 0 x))`] THEN
  REWRITE_TAC[WORD_ZX_BITVAL; BIT_WORD_NOT; DIMINDEX_1; ARITH; BIT_LSB_WORD]);;

(* ------------------------------------------------------------------------- *)
(* Conversions for explicit calculations with terms of the form "word n"     *)
(* where n is a numeral. They all work for arbitrary n and whenever they     *)
(* return "word m", then that will be canonical, i.e. m < 2^wordsize.        *)
(* ------------------------------------------------------------------------- *)

let WORD_WORD_CONV =
  let pth = prove
   (`word n:N word = word(n MOD (2 EXP dimindex(:N)))`,
    REWRITE_TAC[WORD_MOD_SIZE]) in
  fun tm ->
    match tm with
      Comb(Const("word",_),t) when is_numeral t ->
        (GEN_REWRITE_CONV I [pth] THENC
         funpow 2 RAND_CONV (!word_POW2SIZE_CONV) THENC
         RAND_CONV NUM_MOD_CONV) tm
    | _ -> failwith "WORD_WORD_CONV";;

let WORD_IWORD_CONV tm =
  match tm with
   Comb(Const("iword",_),t) when is_intconst t ->
     (REWR_CONV iword THENC
      funpow 4 RAND_CONV (!word_SIZE_CONV) THENC
      funpow 3 RAND_CONV INT_POW_CONV THENC
      funpow 2 RAND_CONV INT_REM_CONV THENC
      GEN_REWRITE_CONV RAND_CONV [NUM_OF_INT_OF_NUM]) tm
  | _ -> failwith "WORD_IWORD_CONV";;

let WORD_SATURATE_CONV =
  let pth = prove
    (`word_saturate n:N word =
        (\t. if n < t then word n else word (t - 1)) (2 EXP dimindex(:N))`,
      REWRITE_TAC[word_saturate; VAL_WORD_UINT_MAX; GT] THEN
      SIMP_TAC[ARITH_RULE `~(m = 0) ==> (m - 1 < n <=> ~(n < m))`;
               EXP_EQ_0; ARITH_EQ; COND_SWAP; word_UINT_MAX])
  and n_tm = `n:num` and n_ty = `:N`
  and conv_cond_t = GEN_REWRITE_CONV I [CONJUNCT1(SPEC_ALL COND_CLAUSES)]
  and conv_cond_f = GEN_REWRITE_CONV I [CONJUNCT2(SPEC_ALL COND_CLAUSES)] in
  fun tm ->
    match tm with
      Comb(Const("word_saturate",
           Tyapp("fun",[_;Tyapp("word",[nty])])),
           (Comb(Const("NUMERAL",_),_) as ntm)) ->
        let th1 = INST [ntm,n_tm] (INST_TYPE [nty,n_ty] pth) in
        let th2 = (RAND_CONV (!word_POW2SIZE_CONV) THENC BETA_CONV THENC
                   RATOR_CONV(LAND_CONV NUM_LT_CONV) THENC
                   (conv_cond_t ORELSEC
                    (conv_cond_f THENC RAND_CONV NUM_SUB_CONV)))
                  (rand(concl th1)) in
        TRANS th1 th2
    | _ -> failwith "WORD_SATURATE_CONV";;

let IWORD_SATURATE_CONV =
  let pth = prove
    (`iword_saturate n:N word =
        (\t. if n < -- &t then word t
             else if &t <= n then word(t - 1)
             else iword n) (2 EXP (dimindex(:N) - 1))`,
      REWRITE_TAC[iword_saturate; IVAL_WORD_INT_MIN; IVAL_WORD_INT_MAX] THEN
      REWRITE_TAC[word_INT_MIN; word_INT_MAX] THEN
      REWRITE_TAC[INT_ARITH `n:int > m - &1 <=> m <= n`] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; WORD_IWORD] THEN
      SIMP_TAC[GSYM INT_OF_NUM_SUB; LE_1; EXP_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      REWRITE_TAC[IWORD_EQ] THEN MATCH_MP_TAC(INTEGER_RULE
       `&2 * x:int = n ==> (--x == x) (mod n)`) THEN
      REWRITE_TAC[GSYM(CONJUNCT2 INT_POW)] THEN
      SIMP_TAC[DIMINDEX_NONZERO; ARITH_RULE `~(n = 0) ==> SUC(n - 1) = n`])
  and n_tm = `n:int` and n_ty = `:N`
  and conv_cond_t = GEN_REWRITE_CONV I [CONJUNCT1(SPEC_ALL COND_CLAUSES)]
  and conv_cond_f = GEN_REWRITE_CONV I [CONJUNCT2(SPEC_ALL COND_CLAUSES)] in
  fun tm ->
    match tm with
      Comb(Const("iword_saturate",
           Tyapp("fun",[_;Tyapp("word",[nty])])),ntm) when is_intconst ntm ->
        let th1 = INST [ntm,n_tm] (INST_TYPE [nty,n_ty] pth) in
        let th2 = (RAND_CONV
                    (RAND_CONV
                      (LAND_CONV(!word_SIZE_CONV) THENC NUM_SUB_CONV) THENC
                     NUM_EXP_CONV) THENC
                   BETA_CONV THENC
                   RATOR_CONV(LAND_CONV INT_LT_CONV) THENC
                   (conv_cond_t ORELSEC
                    (conv_cond_f THENC
                     RATOR_CONV(LAND_CONV INT_LE_CONV) THENC
                     ((conv_cond_t THENC RAND_CONV NUM_SUB_CONV) ORELSEC
                      (conv_cond_f THENC WORD_IWORD_CONV)))))
                  (rand(concl th1)) in
        TRANS th1 th2
    | _ -> failwith "WORD_SATURATE_CONV";;

let WORD_VAL_CONV tm =
  match tm with
    Comb(Const("val",_),Comb(Const("word",_),n)) when is_numeral n ->
     (GEN_REWRITE_CONV I [VAL_WORD] THENC
      funpow 2 RAND_CONV (!word_SIZE_CONV) THENC
      RAND_CONV NUM_EXP_CONV THENC NUM_MOD_CONV) tm
  | _ -> failwith "WORD_VAL_CONV";;

let WORD_IVAL_CONV =
  let pth = prove
   (`ival(word n:N word) =
        (\v. if v < 2 EXP (dimindex (:N) - 1)
             then &v else &v - &2 pow dimindex(:N))
        (val(word n:N word))`,
    REWRITE_TAC[ival])
  and cth1,cth2 = CONJ_PAIR
   (MESON[] `(if T then x:int else y:int) = x /\
             (if F then x:int else y:int) = y`) in
  fun tm ->
   (match tm with
      Comb(Const("ival",_),Comb(Const("word",_),n)) when is_numeral n ->
     (GEN_REWRITE_CONV I [pth] THENC
      RAND_CONV WORD_VAL_CONV THENC
      BETA_CONV THENC
      RATOR_CONV(LAND_CONV
       (RAND_CONV (RAND_CONV
           (LAND_CONV (!word_SIZE_CONV) THENC NUM_SUB_CONV) THENC
         NUM_EXP_CONV) THENC
        NUM_LT_CONV)) THENC
      (GEN_REWRITE_CONV I [cth1] ORELSEC
       (GEN_REWRITE_CONV I [cth2] THENC
        (RAND_CONV o RAND_CONV) (!word_SIZE_CONV) THENC
        RAND_CONV INT_POW_CONV THENC INT_SUB_CONV))) tm
    | _ -> failwith "WORD_IVAL_CONV");;

let WORD_BIT_CONV =
  let pth0 = prove
   (`(ODD(0 DIV 2 EXP k) <=> F) /\
     (ODD(NUMERAL(BIT0 n) DIV 2 EXP 0) <=> F) /\
     (ODD(NUMERAL(BIT1 n) DIV 2 EXP 0) <=> T)`,
    REWRITE_TAC[DIV_0; ODD; EXP; DIV_1] THEN
    REWRITE_TAC[NUMERAL; BIT0; BIT1] THEN
    REWRITE_TAC[ODD; ODD_ADD])
  and pth1 = prove
   (`(ODD(NUMERAL(BIT0 n) DIV 2 EXP SUC k) <=> ODD(NUMERAL n DIV (2 EXP k))) /\
     (ODD(NUMERAL(BIT1 n) DIV 2 EXP SUC k) <=> ODD(NUMERAL n DIV (2 EXP k)))`,
    CONJ_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV) [NUMERAL] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [BIT0; BIT1] THEN
    REWRITE_TAC[EXP; GSYM DIV_DIV] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC) in
  let conv0 = GEN_REWRITE_CONV I [pth0]
  and conv1 = GEN_REWRITE_CONV I [pth1]
  and conva = GEN_REWRITE_CONV I [AND_CLAUSES] in
  let rec conv tm =
    (conv0 ORELSEC
     (funpow 3 RAND_CONV num_CONV THENC
      conv1 THENC
      conv)) tm in
  fun tm ->
    match tm with
       Comb(Comb(Const("bit",_),k),Comb(Const("word",_),n))
       when is_numeral k && is_numeral n ->
     (GEN_REWRITE_CONV I [BIT_WORD] THENC
      BINOP2_CONV (RAND_CONV (!word_SIZE_CONV) THENC NUM_LT_CONV) conv THENC
      conva) tm
    | _ -> failwith "WORD_BIT_CONV";;

let BIT_WORD_PMUL_CONV =
    let main_conv =
    RAND_CONV
     (EXPAND_NSUM_CONV THENC
      DEPTH_BINOP_CONV `(+):num->num->num`
         (BINOP2_CONV
           (RAND_CONV WORD_BIT_CONV THENC GEN_REWRITE_CONV I [BITVAL_CLAUSES])
           (RAND_CONV(LAND_CONV NUM_SUB_CONV THENC WORD_BIT_CONV) THENC
            GEN_REWRITE_CONV I [BITVAL_CLAUSES]) THENC
          NUM_MULT_CONV) THENC
      DEPTH_CONV NUM_ADD_CONV) THENC
    NUM_ODD_CONV in
  let conv =
    GEN_REWRITE_CONV I [BIT_WORD_PMUL] THENC
    LAND_CONV(RAND_CONV DIMINDEX_CONV THENC NUM_LT_CONV) THENC
    ((GEN_REWRITE_CONV I [TAUT `T /\ p <=> p`] THENC main_conv) ORELSEC
     GEN_REWRITE_CONV I [TAUT `F /\ p <=> F`]) in
  fun tm ->
    match tm with
     Comb(Comb(Const("bit",_),i),
          Comb(Comb(Const("word_pmul",_),
                    Comb(Const("word",_),m)),
               Comb(Const("word",_),n)))
     when is_numeral i && is_numeral m && is_numeral n -> conv tm
    | _ -> failwith "BIT_WORD_PMUL_CONV";;


let WORD_EQ_CONV =
   let pth = prove
   (`word(NUMERAL m):N word = (word(NUMERAL n):N word) <=>
     val(word(NUMERAL m):N word) = val(word(NUMERAL n):N word)`,
    REWRITE_TAC[VAL_EQ]) in
  GEN_REWRITE_CONV I [pth] THENC BINOP_CONV WORD_VAL_CONV THENC NUM_EQ_CONV;;

let WORD_ULT_CONV =
  let pth = prove
   (`word_ult (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     val(word(NUMERAL m):N word) < val(word(NUMERAL n):N word)`,
    REWRITE_TAC[word_ult; relational2]) in
  GEN_REWRITE_CONV I [pth] THENC BINOP_CONV WORD_VAL_CONV THENC NUM_LT_CONV;;

let WORD_ULE_CONV =
  let pth = prove
   (`word_ule (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     val(word(NUMERAL m):N word) <= val(word(NUMERAL n):N word)`,
    REWRITE_TAC[word_ule; relational2]) in
  GEN_REWRITE_CONV I [pth] THENC BINOP_CONV WORD_VAL_CONV THENC NUM_LE_CONV;;

let WORD_UGT_CONV =
  let pth = prove
   (`word_ugt (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     val(word(NUMERAL m):N word) > val(word(NUMERAL n):N word)`,
    REWRITE_TAC[word_ugt; relational2]) in
  GEN_REWRITE_CONV I [pth] THENC BINOP_CONV WORD_VAL_CONV THENC NUM_GT_CONV;;

let WORD_UGE_CONV =
  let pth = prove
   (`word_uge (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     val(word(NUMERAL m):N word) >= val(word(NUMERAL n):N word)`,
    REWRITE_TAC[word_uge; relational2]) in
  GEN_REWRITE_CONV I [pth] THENC BINOP_CONV WORD_VAL_CONV THENC NUM_GE_CONV;;

let WORD_ILT_CONV =
  let pth = prove
   (`word_ilt (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     ival(word(NUMERAL m):N word) < ival(word(NUMERAL n):N word)`,
    REWRITE_TAC[word_ilt; irelational2]) in
  GEN_REWRITE_CONV I [pth] THENC BINOP_CONV WORD_IVAL_CONV THENC INT_LT_CONV;;

let WORD_ILE_CONV =
  let pth = prove
   (`word_ile (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     ival(word(NUMERAL m):N word) <= ival(word(NUMERAL n):N word)`,
    REWRITE_TAC[word_ile; irelational2]) in
  GEN_REWRITE_CONV I [pth] THENC BINOP_CONV WORD_IVAL_CONV THENC INT_LE_CONV;;

let WORD_IGT_CONV =
  let pth = prove
   (`word_igt (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     ival(word(NUMERAL m):N word) > ival(word(NUMERAL n):N word)`,
    REWRITE_TAC[word_igt; irelational2]) in
  GEN_REWRITE_CONV I [pth] THENC BINOP_CONV WORD_IVAL_CONV THENC INT_GT_CONV;;

let WORD_IGE_CONV =
  let pth = prove
   (`word_ige (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     ival(word(NUMERAL m):N word) >= ival(word(NUMERAL n):N word)`,
    REWRITE_TAC[word_ige; irelational2]) in
  GEN_REWRITE_CONV I [pth] THENC BINOP_CONV WORD_IVAL_CONV THENC INT_GE_CONV;;

let WORD_ADD_CONV =
  let pth = prove
   (`word_add (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word((NUMERAL m + NUMERAL n) MOD (2 EXP dimindex(:N)))`,
    REWRITE_TAC[word_add; modular; VAL_WORD; WORD_EQ; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV
   (BINOP2_CONV NUM_ADD_CONV (!word_POW2SIZE_CONV) THENC NUM_MOD_CONV);;

let WORD_MUL_CONV =
  let pth = prove
   (`word_mul (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word((NUMERAL m * NUMERAL n) MOD (2 EXP dimindex(:N)))`,
    REWRITE_TAC[word_mul; modular; VAL_WORD; WORD_EQ; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV
   (BINOP2_CONV NUM_MULT_CONV (!word_POW2SIZE_CONV) THENC NUM_MOD_CONV);;

let WORD_SUB_CONV =
  let pth = prove
   (`word_sub (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     (\p. word((NUMERAL m + (p - NUMERAL n MOD p)) MOD p))
     (2 EXP dimindex(:N))`,
    REWRITE_TAC[word_sub; modular; VAL_WORD; WORD_EQ; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(!word_POW2SIZE_CONV) THENC BETA_CONV THENC
  RAND_CONV
   (LAND_CONV
    (RAND_CONV(RAND_CONV NUM_MOD_CONV THENC NUM_SUB_CONV) THENC
     NUM_ADD_CONV) THENC
    NUM_MOD_CONV);;

let WORD_NEG_CONV =
  let pth = prove
   (`word_neg (word(NUMERAL n):N word) =
     (\p. word((p - NUMERAL n MOD p) MOD p))
     (2 EXP dimindex(:N))`,
    REWRITE_TAC[word_neg; word_sub; modular; VAL_WORD; WORD_EQ; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[ADD_CLAUSES]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(!word_POW2SIZE_CONV) THENC BETA_CONV THENC
  RAND_CONV
   (LAND_CONV
    (RAND_CONV NUM_MOD_CONV THENC NUM_SUB_CONV) THENC
    NUM_MOD_CONV);;

let WORD_UDIV_CONV =
  let pth = prove
   (`word_udiv (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     (\p. word((NUMERAL m MOD p) DIV (NUMERAL n MOD p)))
     (2 EXP dimindex(:N))`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UDIV; VAL_WORD] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC(ARITH_RULE
     `m DIV n <= m /\ m < p ==> m DIV n < p`) THEN
    SIMP_TAC[DIV_LE; DIVISION; EXP_EQ_0; ARITH_EQ]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(!word_POW2SIZE_CONV) THENC BETA_CONV THENC
  RAND_CONV(BINOP_CONV NUM_MOD_CONV THENC NUM_DIV_CONV);;

let WORD_UMOD_CONV =
  let pth = prove
   (`word_umod (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     (\p. word((NUMERAL m MOD p) MOD (NUMERAL n MOD p)))
     (2 EXP dimindex(:N))`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UMOD; VAL_WORD] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC(ARITH_RULE
     `m MOD n <= m /\ m < p ==> m MOD n < p`) THEN
    SIMP_TAC[MOD_LE; DIVISION; EXP_EQ_0; ARITH_EQ]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(!word_POW2SIZE_CONV) THENC BETA_CONV THENC
  RAND_CONV(BINOP_CONV NUM_MOD_CONV THENC NUM_MOD_CONV);;

let WORD_UMAX_CONV =
  let pth = prove
   (`word_umax (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     (\p. word(MAX (NUMERAL m MOD p) (NUMERAL n MOD p)))
     (2 EXP dimindex(:N))`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UMAX; VAL_WORD] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[ARITH_RULE `MAX a b < n <=> a < n /\ b < n`] THEN
    SIMP_TAC[DIVISION; EXP_EQ_0; ARITH_EQ]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(!word_POW2SIZE_CONV) THENC BETA_CONV THENC
  RAND_CONV(BINOP_CONV NUM_MOD_CONV THENC NUM_MAX_CONV);;

let WORD_UMIN_CONV =
  let pth = prove
   (`word_umin (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     (\p. word(MIN (NUMERAL m MOD p) (NUMERAL n MOD p)))
     (2 EXP dimindex(:N))`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UMIN; VAL_WORD] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[ARITH_RULE `MIN a b < n <=> a < n \/ b < n`] THEN
    SIMP_TAC[DIVISION; EXP_EQ_0; ARITH_EQ]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(!word_POW2SIZE_CONV) THENC BETA_CONV THENC
  RAND_CONV(BINOP_CONV NUM_MOD_CONV THENC NUM_MIN_CONV);;

let WORD_IMAX_CONV =
  let pth = prove
   (`word_imax (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     if ival(word(NUMERAL m):N word) <= ival(word(NUMERAL n):N word)
     then word((NUMERAL n) MOD (2 EXP dimindex(:N)))
     else word((NUMERAL m) MOD (2 EXP dimindex(:N)))`,
    COND_CASES_TAC THEN
    REWRITE_TAC[GSYM IVAL_EQ; IVAL_WORD_IMAX; WORD_MOD_SIZE] THEN
    ASM_REWRITE_TAC[INT_MAX]) in
  GEN_REWRITE_CONV I [pth] THENC
  RATOR_CONV(LAND_CONV(BINOP_CONV WORD_IVAL_CONV THENC INT_LE_CONV)) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES] THENC
  funpow 2 RAND_CONV (!word_POW2SIZE_CONV) THENC RAND_CONV NUM_MOD_CONV;;

let WORD_IMIN_CONV =
  let pth = prove
   (`word_imin (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     if ival(word(NUMERAL m):N word) <= ival(word(NUMERAL n):N word)
     then word((NUMERAL m) MOD (2 EXP dimindex(:N)))
     else word((NUMERAL n) MOD (2 EXP dimindex(:N)))`,
    COND_CASES_TAC THEN
    REWRITE_TAC[GSYM IVAL_EQ; IVAL_WORD_IMIN; WORD_MOD_SIZE] THEN
    ASM_REWRITE_TAC[INT_MIN]) in
  GEN_REWRITE_CONV I [pth] THENC
  RATOR_CONV(LAND_CONV(BINOP_CONV WORD_IVAL_CONV THENC INT_LE_CONV)) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES] THENC
  funpow 2 RAND_CONV (!word_POW2SIZE_CONV) THENC RAND_CONV NUM_MOD_CONV;;

let WORD_SHL_CONV =
  let pth = prove
   (`word_shl (word(NUMERAL m):N word) (NUMERAL n) =
     (\p. word((NUMERAL m * 2 EXP (NUMERAL n)) MOD p))
     (2 EXP dimindex(:N))`,
    REWRITE_TAC[word_shl; WORD_EQ; VAL_WORD; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV (!word_POW2SIZE_CONV) THENC BETA_CONV THENC
  RAND_CONV
   (LAND_CONV
     (RAND_CONV NUM_EXP_CONV THENC
      NUM_MULT_CONV) THENC
    NUM_MOD_CONV);;

let WORD_USHR_CONV =
  let pth = prove
   (`word_ushr (word(NUMERAL m):N word) (NUMERAL n) =
     (\p. word((NUMERAL m MOD p) DIV (2 EXP NUMERAL n) MOD p))
     (2 EXP dimindex(:N))`,
    REWRITE_TAC[word_ushr; WORD_EQ; VAL_WORD; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV (!word_POW2SIZE_CONV) THENC BETA_CONV THENC
  RAND_CONV
   (LAND_CONV
     (BINOP2_CONV NUM_MOD_CONV NUM_EXP_CONV THENC NUM_DIV_CONV) THENC
    NUM_MOD_CONV);;

let WORD_ISHR_CONV =
  let pth = prove
   (`word_ishr (word(NUMERAL m):N word) (NUMERAL n) =
     iword (ival(word(NUMERAL m):N word) div &2 pow (NUMERAL n))`,
    REWRITE_TAC[word_ishr]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(BINOP2_CONV WORD_IVAL_CONV INT_POW_CONV THENC INT_DIV_CONV) THENC
  WORD_IWORD_CONV;;

let WORD_NOT_CONV =
  let pth = prove
   (`word_not(word n:N word) =
     (\p. word(p - 1 - n MOD p)) (2 EXP dimindex(:N))`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_NOT; VAL_WORD] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    MATCH_MP_TAC(ARITH_RULE `~(p = 0) ==> p - 1 - n < p`) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ]) in
  fun tm ->
   (match tm with
      Comb(Const("word_not",_),Comb(Const("word",_),n)) when is_numeral n ->
     (GEN_REWRITE_CONV I [pth] THENC
      RAND_CONV (!word_POW2SIZE_CONV) THENC BETA_CONV THENC
      RAND_CONV(BINOP2_CONV NUM_SUB_CONV NUM_MOD_CONV THENC
                NUM_SUB_CONV)) tm
    | _ -> failwith "WORD_NOT_CONV");;

let WORD_AND_CONV =
  let pth = prove
   (`?f. ((!n. f _0 n = _0) /\ (!m. f m _0 = _0)) /\
         ((!m n. f (BIT0 m) (BIT0 n) = BIT0(f m n)) /\
          (!m n. f (BIT0 m) (BIT1 n) = BIT0(f m n)) /\
          (!m n. f (BIT1 m) (BIT0 n) = BIT0(f m n)) /\
          (!m n. f (BIT1 m) (BIT1 n) = BIT1(f m n))) /\
         (!m n. word_and (word(NUMERAL m):N word) (word(NUMERAL n)) =
                word(NUMERAL(f m n)))`,
    MP_TAC(prove_general_recursive_function_exists
     `?f. !m n. f m n =
                if m = 0 then 0 else if n = 0 then 0
                else (if m MOD 2 = 1 /\ n MOD 2 = 1 then 1 else 0) +
                     2 * f (m DIV 2) (n DIV 2)`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:num->num->num` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `(!n. f 0 n = 0) /\ (!m. f m 0 = 0) /\
      (!m n. f (2 * m) (2 * n) = 2 * f m n) /\
      (!m n. f (2 * m + 1) (2 * n) = 2 * f m n) /\
      (!m n. f (2 * m) (2 * n + 1) = 2 * f m n) /\
      (!m n. f (2 * m + 1) (2 * n + 1) = 2 * f m n + 1)`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      REWRITE_TAC[ARITH_RULE `(2 * n) DIV 2 = n /\ (2 * n + 1) DIV 2 = n`;
                  ONCE_REWRITE_RULE[MULT_SYM] MOD_MULT_ADD;
                 MOD_MULT; ADD_EQ_0; MULT_EQ_0] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `1 + 2 * n = 2 * n + 1`] THEN
      REPEAT(COND_CASES_TAC THEN REWRITE_TAC[]) THEN
      REWRITE_TAC[ARITH_RULE `0 = 2 * n <=> n = 0`] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      ASM_REWRITE_TAC[COND_ID];
      FIRST_X_ASSUM(K ALL_TAC) THEN STRIP_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[NUMERAL]; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[BIT0; BIT1] THEN ASM_REWRITE_TAC[GSYM MULT_2; ADD1];
      REWRITE_TAC[NUMERAL]] THEN
    REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_AND; BIT_WORD] THEN
    SIMP_TAC[TAUT `(p /\ q <=> p /\ r) <=> (p ==> (q <=> r))`] THEN
    MATCH_MP_TAC BINARY_INDUCT THEN ASM_REWRITE_TAC[DIV_0; ODD] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC BINARY_INDUCT THEN ASM_REWRITE_TAC[DIV_0; ODD] THEN
    X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN CONJ_TAC THEN
    INDUCT_TAC THEN REWRITE_TAC[EXP; DIV_1; ODD_MULT; ARITH; ODD_ADD] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM DIV_DIV] THEN
    REWRITE_TAC[ARITH_RULE `(2 * n) DIV 2 = n /\ (2 * n + 1) DIV 2 = n`;
                MOD_MULT; ONCE_REWRITE_RULE[MULT_SYM] MOD_MULT_ADD] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC)
  and qth = prove
   (`BIT0 _0 = _0`,
    REWRITE_TAC[ARITH_ZERO])
  and nty = `:N` in
  fun tm ->
    (match tm with
      Comb(Comb(Const("word_and",_),
                Comb(Const("word",_),m)),
           Comb(Const("word",_),n))
          when is_numeral m && is_numeral n ->
       let th1 = INST_TYPE
          [hd(snd(dest_type(type_of(rand tm)))),nty] pth in
       let f,bod = dest_exists(concl th1) in
       let pth_base,th2 = CONJ_PAIR(ASSUME bod) in
       let pth_step,pth_trans = CONJ_PAIR th2 in
       let base_conv = GEN_REWRITE_CONV I [pth_base]
       and step_conv = GEN_REWRITE_CONV I [pth_step]
       and fix_conv = GEN_REWRITE_CONV TRY_CONV [qth] in
       let rec conv t =
         (base_conv ORELSEC
          (step_conv THENC RAND_CONV conv THENC fix_conv)) t in
       let th3 = REWR_CONV pth_trans tm in
       let th4 = CONV_RULE(funpow 3 RAND_CONV conv) th3 in
       let th5 = PROVE_HYP th1 (SIMPLE_CHOOSE f th4) in
       CONV_RULE(RAND_CONV WORD_WORD_CONV) th5
     | _ -> failwith "WORD_AND_CONV");;

let WORD_OR_CONV =
  let pth = prove
   (`?f. ((!n. f _0 n = n) /\ (!m. f m _0 = m)) /\
         ((!m n. f (BIT0 m) (BIT0 n) = BIT0(f m n)) /\
          (!m n. f (BIT0 m) (BIT1 n) = BIT1(f m n)) /\
          (!m n. f (BIT1 m) (BIT0 n) = BIT1(f m n)) /\
          (!m n. f (BIT1 m) (BIT1 n) = BIT1(f m n))) /\
         (!m n. word_or (word(NUMERAL m):N word) (word(NUMERAL n)) =
                word(NUMERAL(f m n)))`,
    MP_TAC(prove_general_recursive_function_exists
     `?f. !m n. f m n =
                if m = 0 then n else if n = 0 then m
                else (if m MOD 2 = 1 \/ n MOD 2 = 1 then 1 else 0) +
                     2 * f (m DIV 2) (n DIV 2)`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:num->num->num` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `(!n. f 0 n = n) /\ (!m. f m 0 = m) /\
      (!m n. f (2 * m) (2 * n) = 2 * f m n) /\
      (!m n. f (2 * m + 1) (2 * n) = 2 * f m n + 1) /\
      (!m n. f (2 * m) (2 * n + 1) = 2 * f m n + 1) /\
      (!m n. f (2 * m + 1) (2 * n + 1) = 2 * f m n + 1)`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      REWRITE_TAC[ARITH_RULE `(2 * n) DIV 2 = n /\ (2 * n + 1) DIV 2 = n`;
                  ONCE_REWRITE_RULE[MULT_SYM] MOD_MULT_ADD;
                 MOD_MULT; ADD_EQ_0; MULT_EQ_0] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `1 + 2 * n = 2 * n + 1`] THEN
      REPEAT(COND_CASES_TAC THEN REWRITE_TAC[]) THEN
      ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      TRY(AP_THM_TAC THEN AP_TERM_TAC) THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      ASM_REWRITE_TAC[COND_ID] THEN MESON_TAC[];
      FIRST_X_ASSUM(K ALL_TAC) THEN STRIP_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[NUMERAL]; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[BIT0; BIT1] THEN ASM_REWRITE_TAC[GSYM MULT_2; ADD1];
      REWRITE_TAC[NUMERAL]] THEN
    REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_OR; BIT_WORD] THEN
    SIMP_TAC[TAUT `(p /\ q <=> p /\ r) <=> (p ==> (q <=> r))`] THEN
    MATCH_MP_TAC BINARY_INDUCT THEN ASM_REWRITE_TAC[DIV_0; ODD] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC BINARY_INDUCT THEN ASM_REWRITE_TAC[DIV_0; ODD] THEN
    X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN CONJ_TAC THEN
    INDUCT_TAC THEN REWRITE_TAC[EXP; DIV_1; ODD_MULT; ARITH; ODD_ADD] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM DIV_DIV] THEN
    REWRITE_TAC[ARITH_RULE `(2 * n) DIV 2 = n /\ (2 * n + 1) DIV 2 = n`;
                MOD_MULT; ONCE_REWRITE_RULE[MULT_SYM] MOD_MULT_ADD] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC)
  and qth = prove
   (`BIT0 _0 = _0`,
    REWRITE_TAC[ARITH_ZERO])
  and nty = `:N` in
  fun tm ->
    (match tm with
      Comb(Comb(Const("word_or",_),
                Comb(Const("word",_),m)),
           Comb(Const("word",_),n))
          when is_numeral m && is_numeral n ->
       let th1 = INST_TYPE
          [hd(snd(dest_type(type_of(rand tm)))),nty] pth in
       let f,bod = dest_exists(concl th1) in
       let pth_base,th2 = CONJ_PAIR(ASSUME bod) in
       let pth_step,pth_trans = CONJ_PAIR th2 in
       let base_conv = GEN_REWRITE_CONV I [pth_base]
       and step_conv = GEN_REWRITE_CONV I [pth_step]
       and fix_conv = GEN_REWRITE_CONV TRY_CONV [qth] in
       let rec conv t =
         (base_conv ORELSEC
          (step_conv THENC RAND_CONV conv THENC fix_conv)) t in
       let th3 = REWR_CONV pth_trans tm in
       let th4 = CONV_RULE(funpow 3 RAND_CONV conv) th3 in
       let th5 = PROVE_HYP th1 (SIMPLE_CHOOSE f th4) in
       CONV_RULE(RAND_CONV WORD_WORD_CONV) th5
     | _ -> failwith "WORD_OR_CONV");;

let WORD_XOR_CONV =
  let pth = prove
   (`?f. ((!n. f _0 n = n) /\ (!m. f m _0 = m)) /\
         ((!m n. f (BIT0 m) (BIT0 n) = BIT0(f m n)) /\
          (!m n. f (BIT0 m) (BIT1 n) = BIT1(f m n)) /\
          (!m n. f (BIT1 m) (BIT0 n) = BIT1(f m n)) /\
          (!m n. f (BIT1 m) (BIT1 n) = BIT0(f m n))) /\
         (!m n. word_xor (word(NUMERAL m):N word) (word(NUMERAL n)) =
                word(NUMERAL(f m n)))`,
    MP_TAC(prove_general_recursive_function_exists
     `?f. !m n. f m n =
                if m = 0 then n else if n = 0 then m
                else (if m MOD 2 = 1 <=> n MOD 2 = 1 then 0 else 1) +
                     2 * f (m DIV 2) (n DIV 2)`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:num->num->num` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `(!n. f 0 n = n) /\ (!m. f m 0 = m) /\
      (!m n. f (2 * m) (2 * n) = 2 * f m n) /\
      (!m n. f (2 * m + 1) (2 * n) = 2 * f m n + 1) /\
      (!m n. f (2 * m) (2 * n + 1) = 2 * f m n + 1) /\
      (!m n. f (2 * m + 1) (2 * n + 1) = 2 * f m n)`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      REWRITE_TAC[ARITH_RULE `(2 * n) DIV 2 = n /\ (2 * n + 1) DIV 2 = n`;
                  ONCE_REWRITE_RULE[MULT_SYM] MOD_MULT_ADD;
                 MOD_MULT; ADD_EQ_0; MULT_EQ_0] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `1 + 2 * n = 2 * n + 1`] THEN
      REPEAT(COND_CASES_TAC THEN REWRITE_TAC[]) THEN
      ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      TRY(AP_THM_TAC THEN AP_TERM_TAC) THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      ASM_REWRITE_TAC[COND_ID] THEN MESON_TAC[];
      FIRST_X_ASSUM(K ALL_TAC) THEN STRIP_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[NUMERAL]; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[BIT0; BIT1] THEN ASM_REWRITE_TAC[GSYM MULT_2; ADD1];
      REWRITE_TAC[NUMERAL]] THEN
    REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_XOR; BIT_WORD] THEN
    SIMP_TAC[TAUT `(p /\ q <=> p /\ r) <=> (p ==> (q <=> r))`] THEN
    MATCH_MP_TAC BINARY_INDUCT THEN ASM_REWRITE_TAC[DIV_0; ODD] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC BINARY_INDUCT THEN ASM_REWRITE_TAC[DIV_0; ODD] THEN
    X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN CONJ_TAC THEN
    INDUCT_TAC THEN REWRITE_TAC[EXP; DIV_1; ODD_MULT; ARITH; ODD_ADD] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM DIV_DIV] THEN
    REWRITE_TAC[ARITH_RULE `(2 * n) DIV 2 = n /\ (2 * n + 1) DIV 2 = n`;
                MOD_MULT; ONCE_REWRITE_RULE[MULT_SYM] MOD_MULT_ADD] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC)
  and qth = prove
   (`BIT0 _0 = _0`,
    REWRITE_TAC[ARITH_ZERO])
  and nty = `:N` in
  fun tm ->
    (match tm with
      Comb(Comb(Const("word_xor",_),
                Comb(Const("word",_),m)),
           Comb(Const("word",_),n))
          when is_numeral m && is_numeral n ->
       let th1 = INST_TYPE
          [hd(snd(dest_type(type_of(rand tm)))),nty] pth in
       let f,bod = dest_exists(concl th1) in
       let pth_base,th2 = CONJ_PAIR(ASSUME bod) in
       let pth_step,pth_trans = CONJ_PAIR th2 in
       let base_conv = GEN_REWRITE_CONV I [pth_base]
       and step_conv = GEN_REWRITE_CONV I [pth_step]
       and fix_conv = GEN_REWRITE_CONV TRY_CONV [qth] in
       let rec conv t =
         (base_conv ORELSEC
          (step_conv THENC RAND_CONV conv THENC fix_conv)) t in
       let th3 = REWR_CONV pth_trans tm in
       let th4 = CONV_RULE(funpow 3 RAND_CONV conv) th3 in
       let th5 = PROVE_HYP th1 (SIMPLE_CHOOSE f th4) in
       CONV_RULE(RAND_CONV WORD_WORD_CONV) th5
     | _ -> failwith "WORD_XOR_CONV");;

let WORD_ROL_CONV =
  let pth = prove
   (`word_rol (word(NUMERAL m):N word) n =
     (\n. word_or (word_shl (word(NUMERAL m):N word) n)
                  (word_ushr (word(NUMERAL m):N word) (dimindex (:N) - n)))
     (n MOD dimindex(:N))`,
    REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ROL_MOD] THEN
    SIMP_TAC[WORD_ROL_SHIFTS; DIMINDEX_NONZERO; DIVISION; LT_IMP_LE]) in
  GEN_REWRITE_CONV I [pth] THENC
  (RAND_CONV o RAND_CONV) (!word_SIZE_CONV) THENC
  RAND_CONV NUM_MOD_CONV THENC NUM_REDUCE_CONV THENC
  BINOP2_CONV WORD_SHL_CONV
              ((RAND_CONV o LAND_CONV) (!word_SIZE_CONV) THENC
               RAND_CONV NUM_SUB_CONV THENC WORD_USHR_CONV) THENC
  WORD_OR_CONV;;

let WORD_ROR_CONV =
  let pth = prove
   (`word_ror (word(NUMERAL m):N word) n =
     (\n. word_or (word_ushr (word(NUMERAL m):N word) n)
                  (word_shl (word(NUMERAL m):N word) (dimindex (:N) - n)))
     (n MOD dimindex(:N))`,
    REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ROR_MOD] THEN
    SIMP_TAC[WORD_ROR_SHIFTS; DIMINDEX_NONZERO; DIVISION; LT_IMP_LE]) in
  GEN_REWRITE_CONV I [pth] THENC
  (RAND_CONV o RAND_CONV) (!word_SIZE_CONV) THENC
  RAND_CONV NUM_MOD_CONV THENC NUM_REDUCE_CONV THENC
  BINOP2_CONV WORD_USHR_CONV
              ((RAND_CONV o LAND_CONV) (!word_SIZE_CONV) THENC
               RAND_CONV NUM_SUB_CONV THENC WORD_SHL_CONV) THENC
  WORD_OR_CONV;;

let WORD_ZX_CONV =
  let pth = prove
   (`(word_zx:M word->N word) (word (NUMERAL n)) =
     word (NUMERAL n MOD (2 EXP (MIN (dimindex(:M)) (dimindex(:N)))))`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
    MESON_TAC[MOD_MOD_EXP_MIN; MOD_MOD_REFL]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV
   (RAND_CONV
     (RAND_CONV(BINOP_CONV (!word_SIZE_CONV) THENC
                NUM_MIN_CONV) THENC
      NUM_EXP_CONV) THENC
    NUM_MOD_CONV);;

let WORD_SX_CONV =
  let pth = prove
   (`(word_sx:M word->N word) (word (NUMERAL n)) =
     iword(ival(word(NUMERAL n):M word))`,
    REWRITE_TAC[word_sx]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV WORD_IVAL_CONV THENC
  WORD_IWORD_CONV;;

let WORD_SXFROM_CONV =
   let pth = prove
    (`word_sxfrom (NUMERAL n) (word(NUMERAL x):N word) =
      word_ishr (word_shl (word(NUMERAL x)) (dimindex (:N) - 1 - NUMERAL n))
                (dimindex (:N) - 1 - NUMERAL n)`,
     REWRITE_TAC[word_sxfrom]) in
  GEN_REWRITE_CONV I [pth] THENC
  LAND_CONV (RAND_CONV
   (LAND_CONV(LAND_CONV(!word_SIZE_CONV) THENC NUM_SUB_CONV) THENC
              NUM_SUB_CONV) THENC
    WORD_SHL_CONV) THENC
  RAND_CONV
   (LAND_CONV(LAND_CONV(!word_SIZE_CONV) THENC NUM_SUB_CONV) THENC
              NUM_SUB_CONV) THENC
  WORD_ISHR_CONV;;

let WORD_CAND_CONV =
 let pth = prove
  (`word_cand (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
    if word(NUMERAL m):N word = word 0 \/
       word(NUMERAL n):N word = word 0
    then word 0 else word 1`,
   REWRITE_TAC[WORD_CAND]) in
  GEN_REWRITE_CONV I [pth] THENC
  RATOR_CONV(LAND_CONV
   (BINOP_CONV WORD_EQ_CONV THENC
    GEN_REWRITE_CONV I [OR_CLAUSES])) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES];;

let WORD_COR_CONV =
 let pth = prove
  (`word_cor (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
    if word(NUMERAL m):N word = word 0 /\
       word(NUMERAL n):N word = word 0
    then word 0 else word 1`,
   REWRITE_TAC[WORD_COR]) in
  GEN_REWRITE_CONV I [pth] THENC
  RATOR_CONV(LAND_CONV
   (BINOP_CONV WORD_EQ_CONV THENC
    GEN_REWRITE_CONV I [AND_CLAUSES])) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES];;

let WORD_JOIN_CONV =
 let pth = prove
   (`(word_join:(M)word->(N)word->(P)word)
     (word(NUMERAL m)) (word(NUMERAL n)) =
     word((2 EXP dimindex(:N) * NUMERAL m MOD 2 EXP dimindex(:M) +
           NUMERAL n MOD 2 EXP dimindex(:N)) MOD
          2 EXP dimindex(:P))`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_JOIN; VAL_WORD; MOD_MOD_REFL]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV
   (BINOP2_CONV
      (BINOP2_CONV
         (BINOP2_CONV
           (!word_POW2SIZE_CONV)
           (RAND_CONV(!word_POW2SIZE_CONV) THENC NUM_MOD_CONV) THENC
          NUM_MULT_CONV)
         (RAND_CONV(!word_POW2SIZE_CONV) THENC NUM_MOD_CONV)  THENC
       NUM_ADD_CONV)
      (!word_POW2SIZE_CONV) THENC
    NUM_MOD_CONV);;

let WORD_SUBWORD_CONV =
  let pth = prove
   (`word_subword (word(NUMERAL m):M word) (NUMERAL p,NUMERAL q):N word =
     word((val(word(NUMERAL m):M word) DIV 2 EXP NUMERAL p) MOD
           2 EXP MIN (NUMERAL q) (dimindex (:N)))`,
    REWRITE_TAC[word_subword; GSYM MOD_MOD_EXP_MIN] THEN
    REWRITE_TAC[WORD_EQ; CONG; MOD_MOD_REFL]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV
   (BINOP2_CONV
     (BINOP2_CONV WORD_VAL_CONV NUM_EXP_CONV THENC NUM_DIV_CONV)
     (RAND_CONV (RAND_CONV (!word_SIZE_CONV) THENC NUM_MIN_CONV) THENC
      NUM_EXP_CONV) THENC
    NUM_MOD_CONV);;

let WORD_INSERT_CONV =
 let pth = prove
   (`(word_insert:(M)word->num#num->(N)word->(P)word)
     (word(NUMERAL m)) (NUMERAL pos,NUMERAL len) (word(NUMERAL n)) =
     word((2 EXP (NUMERAL pos + NUMERAL len) *
           val(word(NUMERAL m):M word) DIV 2 EXP (NUMERAL pos + NUMERAL len) +
           2 EXP NUMERAL pos *
           val(word(NUMERAL n):N word) MOD 2 EXP NUMERAL len +
           val(word(NUMERAL m):M word) MOD 2 EXP NUMERAL pos) MOD
          2 EXP dimindex(:P))`,
    REWRITE_TAC[WORD_MOD_SIZE; word_insert]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV
   (BINOP2_CONV
     (BINOP2_CONV
       (BINOP2_CONV (RAND_CONV NUM_ADD_CONV THENC NUM_EXP_CONV)
                    (BINOP2_CONV WORD_VAL_CONV
                             (RAND_CONV NUM_ADD_CONV THENC NUM_EXP_CONV) THENC
                     NUM_DIV_CONV) THENC
        NUM_MULT_CONV)
       (BINOP2_CONV
          (BINOP2_CONV NUM_EXP_CONV
             (BINOP2_CONV WORD_VAL_CONV NUM_EXP_CONV THENC NUM_MOD_CONV) THENC
              NUM_MULT_CONV)
          (BINOP2_CONV WORD_VAL_CONV NUM_EXP_CONV THENC NUM_MOD_CONV) THENC
        NUM_ADD_CONV) THENC
       NUM_ADD_CONV)
     (RAND_CONV (!word_SIZE_CONV) THENC NUM_EXP_CONV) THENC
    NUM_MOD_CONV);;

let WORD_DUPLICATE_CONV =
  let m_ty = `:M` and n_ty = `:N` and m_tm = `m:num` and k_tm = `k:num`
  and pth = prove
   (`dimindex(:N) <= k * dimindex(:M)
           ==> (word_duplicate:M word->N word)(word m) =
               (\t. word((t EXP k - 1) DIV (t - 1) * m MOD t))
               (2 EXP dimindex(:M))`,
     SIMP_TAC[WORD_DUPLICATE; EXP_EXP; MULT_SYM]) in
  fun tm ->
  match tm with
    Comb(Const("word_duplicate",Tyapp("fun",[mty;nty])),
         Comb(Const("word",_),
              (Comb(Const("NUMERAL",_),_) as mtm))) ->
        let m = dest_word_ty mty and n = dest_word_ty nty in
        let k = quo_num (n +/ m -/ num_1) m in
        let th1 =  INST [mtm,m_tm; mk_numeral k,k_tm]
                        (INST_TYPE [mk_finty m,m_ty; mk_finty n,n_ty] pth) in
        let th2 = (BINOP2_CONV
                    (!word_SIZE_CONV)
                    (RAND_CONV(!word_SIZE_CONV) THENC NUM_MULT_CONV) THENC
                   NUM_LE_CONV)
                  (lhand(concl th1)) in
        let th3 = MP th1 (EQT_ELIM th2) in
        let th4 = CONV_RULE(RAND_CONV
          (RAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_EXP_CONV))) th3 in
        let th5 = CONV_RULE(RAND_CONV BETA_CONV) th4 in
        let th6 = CONV_RULE(RAND_CONV(RAND_CONV NUM_REDUCE_CONV)) th5 in
        CONV_RULE(RAND_CONV WORD_WORD_CONV) th6
  | _ -> failwith "WORD_DUPLICATE_CONV";;

let WORD_BITS_OF_WORD_CONV =
  let pth = prove
   (`?f. (!i. f i _0 = {} /\
              (!n. f i (BIT0 n) = f (i + 1) n) /\
              (!n. f i (BIT1 n) = i INSERT f (i + 1) n)) /\
         (!w:N word. bits_of_word w = f 0 (val w))`,
    MP_TAC(prove_general_recursive_function_exists
     `?f. !i n. f i n =
                  if n = 0 then {}
             else if n MOD 2 = 1 then i INSERT f (i + 1) (n DIV 2)
             else f (i + 1) (n DIV 2)`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:num->num->num->bool` THEN
    DISCH_TAC THEN
    GEN_REWRITE_TAC
     (LAND_CONV o BINDER_CONV o LAND_CONV o LAND_CONV o RAND_CONV)
     [GSYM NUMERAL] THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o RAND_CONV o BINOP_CONV o
                     BINDER_CONV o LAND_CONV o RAND_CONV)
     [BIT0; BIT1] THEN
    REWRITE_TAC[ADD1; GSYM MULT_2] THEN MATCH_MP_TAC(TAUT
     `p /\ (p ==> q) ==> p /\ q`) THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM(fun th ->
        GEN_REWRITE_TAC LAND_CONV [th]) THEN
      REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; ARITH_EQ; ARITH_RULE
       `(2 * n + 1) DIV 2 = n /\ (2 * n) DIV 2 = n`] THEN
      REWRITE_TAC[MOD_MULT] THEN
      ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MOD_MULT_ADD] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[];
      POP_ASSUM(K ALL_TAC) THEN
      REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
    X_GEN_TAC `w:N word` THEN REWRITE_TAC[EXTENSION] THEN
    SUBGOAL_THEN
     `!k i. i IN f k (val w) <=> k <= i /\ (i - k) IN bits_of_word(w:N word)`
    MP_TAC THENL [ALL_TAC; MESON_TAC[SUB_0; LE_0]] THEN
    REWRITE_TAC[bits_of_word; BIT_VAL] THEN
    SPEC_TAC(`val(w:N word)`,`n:num`) THEN
    MATCH_MP_TAC BINARY_INDUCT THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    REWRITE_TAC[DIV_0; NOT_IN_EMPTY; ARITH] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[IN_INSERT; AND_FORALL_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `i:num`] THEN
    ASM_CASES_TAC `i:num = k` THEN
    ASM_REWRITE_TAC[LE_REFL; SUB_REFL; ARITH_RULE `~(k + 1 <= k)`] THEN
    REWRITE_TAC[EXP; DIV_1; ODD_ADD; ODD_MULT; ARITH] THEN
    ASM_CASES_TAC `k:num <= i` THEN ASM_REWRITE_TAC[] THENL
     [ALL_TAC; ASM_ARITH_TAC] THEN
    ASM_CASES_TAC `k + 1 <= i` THEN ASM_REWRITE_TAC[] THENL
     [ALL_TAC; ASM_ARITH_TAC] THEN
    SUBGOAL_THEN `i - k = SUC(i - (k + 1))` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[EXP; GSYM DIV_DIV]] THEN
    REWRITE_TAC[ARITH_RULE `(2 * n + 1) DIV 2 = n /\ (2 * n) DIV 2 = n`])
  and nty = `:N` in
  fun tm ->
    (match tm with
      Comb(Const("bits_of_word",_),Comb(Const("word",_),n))
          when is_numeral n ->
       let th1 = INST_TYPE
          [hd(snd(dest_type(type_of(rand tm)))),nty] pth in
       let f,bod = dest_exists(concl th1) in
       let pth_clauses,th2 = CONJ_PAIR(ASSUME bod) in
       let pth_z,pth_o = CONJ_PAIR(SPEC_ALL pth_clauses) in
       let pth_0,pth_1 = CONJ_PAIR pth_o in
       let conv_z = GEN_REWRITE_CONV I [pth_z]
       and conv_0 = GEN_REWRITE_CONV I [pth_0]
       and conv_1 = GEN_REWRITE_CONV I [pth_1] in
       let rec conv t =
        (conv_z ORELSEC
         (conv_0 THENC LAND_CONV NUM_ADD_CONV THENC conv) ORELSEC
         (conv_1 THENC RAND_CONV(LAND_CONV NUM_ADD_CONV THENC conv))) t in
       let th3 = REWR_CONV th2 tm in
       let th4 = CONV_RULE(RAND_CONV(RAND_CONV WORD_VAL_CONV)) th3 in
       let th5 = GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [NUMERAL] th4 in
       let th6 = CONV_RULE(RAND_CONV conv) th5 in
       PROVE_HYP th1 (SIMPLE_CHOOSE f th6)
     | _ -> failwith "WORD_BITS_OF_WORD_CONV");;

let WORD_POPCOUNT_CONV =
  let pth = prove
   (`?f. (f _0 = 0 /\
          (!n. f (BIT0 n) = f n) /\
          (!n. f (BIT1 n) = SUC(f n))) /\
         (!w:N word. word_popcount w = f (val w))`,
    MP_TAC(prove_general_recursive_function_exists
     `?f. !n. f n =
                  if n = 0 then 0
             else if n MOD 2 = 1 then SUC(f (n DIV 2))
             else f (n DIV 2)`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:num->num` THEN
    DISCH_TAC THEN
    GEN_REWRITE_TAC
     (LAND_CONV o LAND_CONV o LAND_CONV o RAND_CONV)
     [GSYM NUMERAL] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o BINOP_CONV o
                     BINDER_CONV o LAND_CONV o RAND_CONV)
     [BIT0; BIT1] THEN
    REWRITE_TAC[ADD1; GSYM MULT_2] THEN MATCH_MP_TAC(TAUT
     `p /\ (p ==> q) ==> p /\ q`) THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM(fun th ->
        GEN_REWRITE_TAC LAND_CONV [th]) THEN
      REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; ARITH_EQ; ARITH_RULE
       `(2 * n + 1) DIV 2 = n /\ (2 * n) DIV 2 = n`] THEN
      REWRITE_TAC[MOD_MULT] THEN
      ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MOD_MULT_ADD] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[ADD1];
      POP_ASSUM(K ALL_TAC) THEN
      REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
    X_GEN_TAC `w:N word` THEN REWRITE_TAC[word_popcount] THEN
    REWRITE_TAC[bits_of_word; BIT_VAL] THEN
    SUBGOAL_THEN `!n. {i | ODD(n DIV 2 EXP i)} HAS_SIZE f n` MP_TAC THENL
     [ALL_TAC; SIMP_TAC[HAS_SIZE]] THEN
    MATCH_MP_TAC BINARY_INDUCT THEN
    ASM_REWRITE_TAC[HAS_SIZE; DIV_0; ODD; EMPTY_GSPEC;
                    FINITE_EMPTY; CARD_CLAUSES] THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!P. {i | P i} = {i | i = 0 /\ P 0} UNION IMAGE SUC {i | P(SUC i)}`
     (fun th -> ONCE_REWRITE_TAC[th])
    THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; IN_IMAGE] THEN
      MESON_TAC[num_CASES];
      REWRITE_TAC[EXP; DIV_1; ODD_ADD; ODD_MULT; ARITH]] THEN
    REWRITE_TAC[EMPTY_GSPEC; SING_GSPEC; GSYM DIV_DIV] THEN
    REWRITE_TAC[ARITH_RULE `(2 * n + 1) DIV 2 = n /\ (2 * n) DIV 2 = n`] THEN
    REWRITE_TAC[UNION_EMPTY; INSERT_UNION_EQ] THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_IMAGE; CARD_CLAUSES] THEN
    REWRITE_TAC[IN_IMAGE; NOT_SUC; ADD1; EQ_ADD_RCANCEL] THEN
    ASM_SIMP_TAC[CARD_IMAGE_INJ; SUC_INJ])
  and nty = `:N` in
  fun tm ->
    (match tm with
      Comb(Const("word_popcount",_),Comb(Const("word",_),n))
          when is_numeral n ->
       let th1 = INST_TYPE
          [hd(snd(dest_type(type_of(rand tm)))),nty] pth in
       let f,bod = dest_exists(concl th1) in
       let pth_clauses,th2 = CONJ_PAIR(ASSUME bod) in
       let pth_z,pth_o = CONJ_PAIR(SPEC_ALL pth_clauses) in
       let pth_0,pth_1 = CONJ_PAIR pth_o in
       let conv_z = GEN_REWRITE_CONV I [pth_z]
       and conv_0 = GEN_REWRITE_CONV I [pth_0]
       and conv_1 = GEN_REWRITE_CONV I [pth_1] in
       let rec conv t =
        (conv_z ORELSEC
         (conv_0 THENC conv) ORELSEC
         (conv_1 THENC RAND_CONV conv THENC NUM_SUC_CONV)) t in
       let th3 = REWR_CONV th2 tm in
       let th4 = CONV_RULE(RAND_CONV(RAND_CONV WORD_VAL_CONV)) th3 in
       let th5 = GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [NUMERAL] th4 in
       let th6 = CONV_RULE(RAND_CONV conv) th5 in
       PROVE_HYP th1 (SIMPLE_CHOOSE f th6)
     | _ -> failwith "WORD_POPCOUNT_CONV");;

let WORD_EVENPARITY_CONV =
  let conv =
    GEN_REWRITE_CONV I [word_evenparity] THENC
    RAND_CONV WORD_POPCOUNT_CONV THENC
    NUM_EVEN_CONV in
  fun tm ->
   (match tm with
     Comb(Const("word_evenparity",_),Comb(Const("word",_),n))
      when is_numeral n -> conv tm
    | _ -> failwith "WORD_EVENPARITY_CONV");;

let WORD_ODDPARITY_CONV =
  let conv =
    GEN_REWRITE_CONV I [word_oddparity] THENC
    RAND_CONV WORD_POPCOUNT_CONV THENC
    NUM_ODD_CONV in
  fun tm ->
   (match tm with
     Comb(Const("word_oddparity",_),Comb(Const("word",_),n))
      when is_numeral n -> conv tm
    | _ -> failwith "WORD_ODDPARITY_CONV");;

let WORD_CTZ_CONV =
  let ctz =
    let rec ctza a n =
      if mod_num n num_2 =/ num_0 then ctza (a + 1) (quo_num n num_2) else a in
    fun n -> ctza 0 n
  and pth_0 = prove
    (`!(a:N word). val a = 0 ==> word_ctz a = dimindex(:N)`,
     SIMP_TAC[VAL_EQ_0; WORD_CTZ_0])
  and pth = prove
   (`!(a:N word) v.
        val a = v
        ==> !n e. 2 EXP n = e /\ v MOD (2 * e) = e ==> word_ctz a = n`,
    REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[IMP_CONJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM(CONJUNCT2 EXP); ADD1] THEN
    REWRITE_TAC[WORD_CTZ_UNIQUE_VAL]) in
  fun tm ->
    match tm with
      Comb(Const("word_ctz",_),Comb(Const("word",_),t))
               when is_numeral t ->
        let th1 = ISPEC (rand tm) pth in
        let th2 = WORD_VAL_CONV(lhand(lhand(snd(dest_forall(concl th1))))) in
        let mtm = rand(concl th2) in
        let m = dest_numeral mtm in
        if m =/ num_0 then
          CONV_RULE (RAND_CONV(!word_SIZE_CONV)) (MATCH_MP pth_0 th2)
        else
          let th3 = MP (SPEC mtm th1) th2 in
          let n = ctz m in
          let th4 = SPECL [mk_small_numeral n; mk_numeral(pow2 n)] th3 in
          MP th4 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th4))))
  | _ -> failwith "WORD_CTZ_CONV";;

let WORD_CLZ_CONV =
  let clz k =
    let m = pow2 k in
    let rec clza a n =
      if n </ m then clza (a + 1) (num_2 */ n) else a in
    fun n ->
      if n =/ num_0 then k else min k (clza (-1) n)
  and pth_0 = prove
    (`!(a:N word). val a = 0 ==> word_clz a = dimindex(:N)`,
     SIMP_TAC[VAL_EQ_0; WORD_CLZ_0])
  and pth = prove
   (`!(a:N word) v.
        val a = v
        ==> !n d. n + 1 + d = dimindex(:N) /\ v DIV (2 EXP d) = 1
                  ==> word_clz a = n`,
    REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC WORD_CLZ_UNIQUE_VAL THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[ARITH_RULE `n + 1 + d = N ==> N - n - 1 = d`]) in
  fun tm ->
    match tm with
      Comb(Const("word_clz",_),Comb(Const("word",_),t))
               when is_numeral t ->
        let th1 = ISPEC (rand tm) pth in
        let th2 = WORD_VAL_CONV(lhand(lhand(snd(dest_forall(concl th1))))) in
        let mtm = rand(concl th2) in
        let m = dest_numeral mtm in
        if m =/ num_0 then
          CONV_RULE (RAND_CONV(!word_SIZE_CONV)) (MATCH_MP pth_0 th2)
        else
          let th3 = MP (SPEC mtm th1) th2 in
          let th4 = CONV_RULE
           (BINDER_CONV(BINDER_CONV(LAND_CONV(LAND_CONV
               (RAND_CONV(!word_SIZE_CONV)))))) th3 in
          let btm = lhand(lhand(snd(strip_forall(concl th4)))) in
          let e = dest_small_numeral(rand btm) in
          let n = clz e m in
          let d = e - (n + 1) in
          let th5 = SPECL [mk_small_numeral n; mk_small_numeral d] th4 in
          MP th5 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th5))))
  | _ -> failwith "WORD_CLZ_CONV";;

let WORD_BYTEREVERSE_CONV =
  let pth = prove
   (`!n. word_bytereverse(word (NUMERAL n):((((N)tybit0)tybit0)tybit0)word) =
         word(nsum (0..8*dimindex(:N)-1)
               (\i. 2 EXP i *
                    bitval(ODD(NUMERAL n DIV
                        2 EXP (8 * (dimindex(:N) - 1 - i DIV 8) + i MOD 8)))))`,
    GEN_TAC THEN GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
    REWRITE_TAC[BIT_WORD_BYTEREVERSE; BIT_WORD] THEN
    REWRITE_TAC[DIMINDEX_TYBIT0; ARITH_RULE `2 * 2 * 2 * n = 8 * n`] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p /\ (q <=> q') ==> (p /\ q <=> q')`) THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [ODD_MOD] THEN
    SIMP_TAC[DIGITSUM_DIV_MOD; FINITE_NUMSEG; BITVAL_BOUND_ALT] THEN
    ASM_SIMP_TAC[IN_NUMSEG; LE_0; ARITH_RULE `i < n ==> i <= n - 1`] THEN
    REWRITE_TAC[BITVAL_EQ_1]) in
  GEN_REWRITE_CONV I [pth] THENC
  DEPTH_CONV
   ((!word_SIZE_CONV) ORELSEC NUM_MULT_CONV ORELSEC NUM_SUB_CONV) THENC
  RAND_CONV EXPAND_NSUM_CONV THENC
  DEPTH_CONV(GEN_REWRITE_CONV I [BITVAL_CLAUSES] ORELSEC NUM_RED_CONV);;

let WORD_REVERSEFIELDS_CONV =
  let pth = (SPECL [`NUMERAL b`; `NUMERAL n`] o prove)
   (`!b n.
        word_reversefields b (word n:N word) =
        word(nsum (0..dimindex(:N)-1)
          (\i. 2 EXP i *
               bitval(ODD(n DIV
               2 EXP (if i < b * dimindex(:N) DIV b
                      then b * (dimindex(:N) DIV b - 1 - i DIV b) + i MOD b
                      else i)))))`,
    REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
    REWRITE_TAC[BIT_WORD_REVERSEFIELDS; BIT_WORD] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p /\ (q <=> q') ==> (p /\ q <=> q')`) THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `b = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; LT] THEN
      ASM_CASES_TAC `dimindex (:N) DIV b = 0` THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; LT] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ARITH_RULE
       `b * (x + 1) <= n /\ m < b ==> b * x + m < n`) THEN
      ASM_SIMP_TAC[MOD_LT_EQ; GSYM LDIV_LT_EQ] THEN ASM_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [ODD_MOD] THEN
      SIMP_TAC[DIGITSUM_DIV_MOD; FINITE_NUMSEG; BITVAL_BOUND_ALT] THEN
      ASM_SIMP_TAC[IN_NUMSEG; LE_0; ARITH_RULE `i < n ==> i <= n - 1`] THEN
      REWRITE_TAC[BITVAL_EQ_1]]) in
  GEN_REWRITE_CONV I [pth] THENC
  DEPTH_CONV
   ((!word_SIZE_CONV) ORELSEC NUM_MULT_CONV ORELSEC NUM_SUB_CONV) THENC
  RAND_CONV EXPAND_NSUM_CONV THENC
  DEPTH_CONV(GEN_REWRITE_CONV I [BITVAL_CLAUSES] ORELSEC NUM_RED_CONV);;

let WORD_PMUL_CONV =
  let in_conv =
    GEN_REWRITE_CONV I [GSYM(CONJUNCT2 WORD_PMUL_ZX)] THENC
    RAND_CONV WORD_ZX_CONV
  and base_conv =
    GEN_REWRITE_CONV I [CONJUNCT2 WORD_PMUL_0]
  and step_conv =
    GEN_REWRITE_CONV I [WORD_PMUL_STEP] THENC
    BINOP2_CONV
     (RATOR_CONV(LAND_CONV BIT_WORD_CONV) THENC
      GEN_REWRITE_CONV I [COND_CLAUSES])
     (BINOP2_CONV (WORD_USHR_CONV) WORD_SHL_CONV) in
  let rec conv tm =
    try base_conv tm with Failure _ ->
    (step_conv THENC RAND_CONV conv THENC WORD_XOR_CONV) tm in
  let fullconv = in_conv THENC conv in
  fun tm ->
    match tm with
      Comb(Comb(Const("word_pmul",_),
                Comb(Const("word",_),m)),
            Comb(Const("word",_),n))
      when is_numeral m && is_numeral n -> fullconv tm
  | _ -> failwith "WORD_PMUL_CONV";;

let WORD_JSHL_CONV =
  let pth = prove
   (`word_jshl (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word_shl (word(NUMERAL m):N word)
              (val(word(NUMERAL n):N word) MOD dimindex (:N))`,
    REWRITE_TAC[word_jshl]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(BINOP2_CONV WORD_VAL_CONV (!word_SIZE_CONV) THENC
            NUM_MOD_CONV) THENC
  WORD_SHL_CONV;;

let WORD_JSHR_CONV =
  let pth = prove
   (`word_jshr (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word_ishr (word(NUMERAL m):N word)
               (val(word(NUMERAL n):N word) MOD dimindex (:N))`,
    REWRITE_TAC[word_jshr]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(BINOP2_CONV WORD_VAL_CONV (!word_SIZE_CONV) THENC
            NUM_MOD_CONV) THENC
  WORD_ISHR_CONV;;

let WORD_JUSHR_CONV =
  let pth = prove
   (`word_jushr (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word_ushr (word(NUMERAL m):N word)
               (val(word(NUMERAL n):N word) MOD dimindex (:N))`,
    REWRITE_TAC[word_jushr]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(BINOP2_CONV WORD_VAL_CONV (!word_SIZE_CONV) THENC
            NUM_MOD_CONV) THENC
  WORD_USHR_CONV;;

let WORD_JROL_CONV =
  let pth = prove
   (`word_jrol (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word_rol (word(NUMERAL m):N word) (val(word(NUMERAL n):N word))`,
    REWRITE_TAC[word_jrol]) in
  GEN_REWRITE_CONV I [pth] THENC RAND_CONV WORD_VAL_CONV THENC
  WORD_ROL_CONV;;

let WORD_JROR_CONV =
  let pth = prove
   (`word_jror (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word_ror (word(NUMERAL m):N word) (val(word(NUMERAL n):N word))`,
    REWRITE_TAC[word_jror]) in
  GEN_REWRITE_CONV I [pth] THENC RAND_CONV WORD_VAL_CONV THENC
  WORD_ROR_CONV;;

let WORD_JDIV_CONV =
  let pth = prove
   (`word_jdiv (word(NUMERAL m):N word) (word(NUMERAL n)) =
     (\a b. iword((int_sgn a * int_sgn b) * (abs a div abs b)))
     (ival(word(NUMERAL m):N word)) (ival(word(NUMERAL n):N word))`,
    REWRITE_TAC[word_jdiv; imodular; GSYM INT_MUL_ASSOC]) in
  GEN_REWRITE_CONV I [pth] THENC
  RATOR_CONV(RAND_CONV WORD_IVAL_CONV THENC BETA_CONV) THENC
  RAND_CONV WORD_IVAL_CONV THENC BETA_CONV THENC
  RAND_CONV(COMB2_CONV
             (RAND_CONV (BINOP_CONV INT_SGN_CONV THENC INT_MUL_CONV))
             (BINOP_CONV INT_ABS_CONV THENC INT_DIV_CONV) THENC
            INT_MUL_CONV) THENC
  WORD_IWORD_CONV;;

let WORD_JREM_CONV =
  let pth = prove
   (`word_jrem (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word_sub (word (NUMERAL m))
              (word_mul (word_jdiv (word (NUMERAL m)) (word (NUMERAL n)))
                        (word (NUMERAL n)))`,
    REWRITE_TAC[word_jrem]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV (LAND_CONV WORD_JDIV_CONV THENC WORD_MUL_CONV) THENC
  WORD_SUB_CONV;;

let word_red_conv_list =
 [`word(NUMERAL n):N word`,CHANGED_CONV WORD_WORD_CONV;
  `word_saturate(NUMERAL n):N word`,WORD_SATURATE_CONV;
  `iword i:N word`,WORD_IWORD_CONV;
  `iword_saturate(n):N word`,IWORD_SATURATE_CONV;
  `val(w:N word)`,WORD_VAL_CONV;
  `ival(w:N word)`,WORD_IVAL_CONV;
  `bit (NUMERAL k) (word(NUMERAL n):N word)`,WORD_BIT_CONV;
  `word(NUMERAL m):N word = word(NUMERAL n)`,WORD_EQ_CONV;
  `word_ult (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_ULT_CONV;
  `word_ule (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_ULE_CONV;
  `word_ugt (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_UGT_CONV;
  `word_uge (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_UGE_CONV;
  `word_ilt (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_ILT_CONV;
  `word_ile (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_ILE_CONV;
  `word_igt (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_IGT_CONV;
  `word_ige (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_IGE_CONV;
  `word_neg (word(NUMERAL n):N word)`,WORD_NEG_CONV;
  `word_add (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_ADD_CONV;
  `word_mul (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_MUL_CONV;
  `word_sub (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_SUB_CONV;
  `word_udiv (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_UDIV_CONV;
  `word_umod (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_UMOD_CONV;
  `word_umax (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_UMAX_CONV;
  `word_umin (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_UMIN_CONV;
  `word_imax (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_IMAX_CONV;
  `word_imin (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_IMIN_CONV;
  `word_shl (word(NUMERAL m):N word) (NUMERAL n)`,WORD_SHL_CONV;
  `word_ushr (word(NUMERAL m):N word) (NUMERAL n)`,WORD_USHR_CONV;
  `word_ishr (word(NUMERAL m):N word) (NUMERAL n)`,WORD_ISHR_CONV;
  `word_not (word(NUMERAL n):N word)`,WORD_NOT_CONV;
  `word_and (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_AND_CONV;
  `word_or (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_OR_CONV;
  `word_xor (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_XOR_CONV;
  `word_rol (word(NUMERAL m):N word) (NUMERAL n)`,WORD_ROL_CONV;
  `word_ror (word(NUMERAL m):N word) (NUMERAL n)`,WORD_ROR_CONV;
  `word_zx (word(NUMERAL n):N word)`,WORD_ZX_CONV;
  `word_sx (word(NUMERAL n):N word)`,WORD_SX_CONV;
  `word_sxfrom (NUMERAL m) (word(NUMERAL n):N word)`,WORD_SXFROM_CONV;
  `word_cand (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_CAND_CONV;
  `word_cor (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_COR_CONV;
  `word_join (word(NUMERAL m):M word) (word(NUMERAL n):N word)`,
              WORD_JOIN_CONV;
  `word_subword (word(NUMERAL m):M word) (NUMERAL p,NUMERAL q):N word`,
              WORD_SUBWORD_CONV;
  `word_insert (word(NUMERAL m):M word) (NUMERAL p,NUMERAL q)
               (word(NUMERAL n):N word):P word`,
              WORD_INSERT_CONV;
  `word_duplicate (word(NUMERAL m):M word):N word`,WORD_DUPLICATE_CONV;
  `bits_of_word (word(NUMERAL n):N word)`,WORD_BITS_OF_WORD_CONV;
  `word_popcount (word(NUMERAL n):N word)`,WORD_POPCOUNT_CONV;
  `word_evenparity (word(NUMERAL n):N word)`,WORD_EVENPARITY_CONV;
  `word_oddparity (word(NUMERAL n):N word)`,WORD_ODDPARITY_CONV;
  `word_ctz (word(NUMERAL n):N word)`,WORD_CTZ_CONV;
  `word_clz (word(NUMERAL n):N word)`,WORD_CLZ_CONV;
  `word_bytereverse (word(NUMERAL n):((((N)tybit0)tybit0)tybit0)word)`,
              WORD_BYTEREVERSE_CONV;
  `word_reversefields (NUMERAL b) (word(NUMERAL n):N word)`,
              WORD_REVERSEFIELDS_CONV;
  `(word_pmul:M word->N word->P word) (word(NUMERAL m)) (word(NUMERAL n))`,
              WORD_PMUL_CONV;
  `word_jshl (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_JSHL_CONV;
  `word_jshr (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_JSHR_CONV;
  `word_jushr (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_JUSHR_CONV;
  `word_jrol (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_JROL_CONV;
  `word_jror (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_JROR_CONV;
  `word_jdiv (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_JDIV_CONV;
  `word_jrem (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_JREM_CONV];;

let WORD_RED_CONV =
  let gconv_net = itlist (uncurry net_of_conv) word_red_conv_list (basic_net()) in
  REWRITES_CONV gconv_net;;

let WORD_REDUCE_CONV =
  DEPTH_CONV WORD_RED_CONV;;

let word_compute_add_convs =
  let convlist = map (fun pat,the_conv ->
    let c,args = strip_comb pat in (c,length args,the_conv))
    word_red_conv_list in
  fun (compset:Compute.compset) ->
    itlist (fun newc () -> Compute.add_conv newc compset) convlist ();;

let WORD_COMPUTE_CONV =
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  word_compute_add_convs cs;
  Compute.WEAK_CBV_CONV cs;;

(* ------------------------------------------------------------------------- *)
(* Alternative returning signed words.                                       *)
(* ------------------------------------------------------------------------- *)

let WORD_TO_IWORD_CONV =
  let pth = prove
   (`word(NUMERAL n):N word = iword(ival(word(NUMERAL n):N word))`,
    REWRITE_TAC[IWORD_IVAL]) in
  GEN_REWRITE_CONV I [pth] THENC RAND_CONV WORD_IVAL_CONV;;

let WORD_IREDUCE_CONV =
  WORD_REDUCE_CONV THENC ONCE_DEPTH_CONV WORD_TO_IWORD_CONV;;

(* ------------------------------------------------------------------------- *)
(* Expanding a natural number sum in a more "balanced" way.                  *)
(* ------------------------------------------------------------------------- *)

let EXPAND_NSUM_BALANCE_CONV =
  let op = `(+):num->num->num` in
  let dest = dest_binop op
  and mk = mk_binop op
  and lmk = list_mk_binop op
  and PRV = AC ADD_AC in
  let rec balance tm =
    let tms = striplist dest tm in
    let n = length tms in
    if n <= 3 then tm else
    let tms1,tms2 = chop_list (n / 2) tms in
    mk (balance(lmk tms1)) (balance(lmk tms2)) in
  fun tm ->
    let th = EXPAND_NSUM_CONV tm in
    let tm' = rand(concl th) in
    let th' = PRV(mk_eq(tm',balance tm')) in
    TRANS th th';;

(* ------------------------------------------------------------------------- *)
(* Comparison predicates expressed via the top bit.                          *)
(* ------------------------------------------------------------------------- *)

let WORD_COMPARISON_ULT = prove
 (`!(x:N word) (y:N word).
        val x < val y <=>
        bit (dimindex(:N)-1)
            (word_or (word_and (word_not x) y)
                     (word_and (word_or (word_not x) y) (word_sub x y)))`,
  CONV_TAC WORD_ARITH);;

let WORD_COMPARISON_ULE = prove
 (`!(x:N word) (y:N word).
        val x <= val y <=>
        bit (dimindex(:N)-1)
            (word_and (word_or (word_not x) y)
                      (word_or (word_xor x y) (word_not(word_sub y x))))`,
  CONV_TAC WORD_ARITH);;

let WORD_COMPARISON_ILT = prove
 (`!(x:N word) (y:N word).
        ival x < ival y <=>
        bit (dimindex(:N)-1)
            (word_or (word_and x (word_not y))
                     (word_and (word_not(word_xor x y)) (word_sub x y)))`,
  CONV_TAC WORD_ARITH);;

let WORD_COMPARISON_ILE = prove
 (`!(x:N word) (y:N word).
        ival x <= ival y <=>
        bit (dimindex(:N)-1)
            (word_and (word_or x (word_not y))
                      (word_or (word_xor x y) (word_not(word_sub y x))))`,
  CONV_TAC WORD_ARITH);;

let WORD_COMPARISON_NE = prove
 (`!(x:N word) (y:N word).
        ~(x = y) <=>
        bit (dimindex(:N)-1)
            (word_or (word_xor x y) (word_neg(word_xor x y)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIT_WORD_OR_NEG; GSYM NOT_LE] THEN
  SIMP_TAC[DIMINDEX_NONZERO; LT_REFL; ARITH_RULE
   `~(n = 0) ==> (x <= n - 1 <=> x < n)`] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_XOR] THEN MESON_TAC[]);;

let WORD_COMPARISON_EQ = prove
 (`!(x:N word) (y:N word).
        x = y <=>
        bit (dimindex(:N)-1)
            (word_not((word_or (word_xor x y) (word_neg(word_xor x y)))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[BIT_WORD_NOT; BIT_WORD_OR_NEG; GSYM NOT_LE] THEN
  SIMP_TAC[DIMINDEX_NONZERO; LT_REFL; ARITH_RULE
   `~(n = 0) ==> (x <= n - 1 <=> x < n)`] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_XOR] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Convert a natural number expression to the form "val(some_word)".         *)
(* Adjust the word size in val(...) to be possibly larger.                   *)
(* Convert a natural number atom m = n, m < n etc. to word form.             *)
(* ------------------------------------------------------------------------- *)

let WORDIFY_CONV =
  let m_ty = `:M` and n_ty = `:N` and p_ty = `:P` and num_ty = `:num`
  and and_th = TAUT `T /\ T <=> T`
  and pth_bitval = prove
   (`!b. bitval b = val(word(bitval b):1 word)`,
    REWRITE_TAC[VAL_WORD_BITVAL])
  and pth_add = prove
   (`dimindex(:M) < dimindex(:P) /\ dimindex(:N) < dimindex(:P)
     ==> !x y. val(x:M word) + val(y:N word) =
               val(word_add (word_zx x) (word_zx y):P word)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_ZX_GEN] THEN
    CONV_TAC MOD_DOWN_CONV THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    TRANS_TAC LTE_TRANS `2 EXP dimindex(:M) + 2 EXP dimindex(:N)` THEN
    SIMP_TAC[LT_ADD2; VAL_BOUND] THEN
    TRANS_TAC LE_TRANS `2 EXP SUC(MAX (dimindex(:M)) (dimindex(:N)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[EXP; MULT_2] THEN MATCH_MP_TAC LE_ADD2 THEN CONJ_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC)
  and pth_mul = prove
   (`dimindex(:M) + dimindex(:N) <= dimindex(:P)
     ==> !x y. val(x:M word) * val(y:N word) =
               val(word_mul (word_zx x) (word_zx y):P word)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_ZX_GEN] THEN
    CONV_TAC MOD_DOWN_CONV THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    TRANS_TAC LTE_TRANS `2 EXP (dimindex (:M) + dimindex (:N))` THEN
    ASM_REWRITE_TAC[LE_EXP; ARITH_EQ] THEN REWRITE_TAC[EXP_ADD] THEN
    MATCH_MP_TAC LT_MULT2 THEN REWRITE_TAC[VAL_BOUND]) in
  let log2 =
    let rec log2 n m i =
      if n </ m then i else log2 n (num_2 */ m) (i + 1) in
    fun n -> num(log2 (abs_num n) num_1 0) in
  let rec conv tm =
    match tm with
      Comb(Const("bitval",_),_) ->
          GEN_REWRITE_CONV I [pth_bitval] tm
    | Comb(Const("val",_),Comb(Const("word",_),_)) ->
          TRY_CONV(RAND_CONV(RAND_CONV conv)) tm
    | Comb(Const("val",_),_) -> REFL tm
    | Comb(Const("NUMERAL",_),_) ->
        let n = max_num num_1 (log2(dest_numeral tm)) in
        let th1 = SPEC tm (INST_TYPE [mk_finty n,n_ty] VAL_WORD_EQ) in
        let th2 =
         (RAND_CONV(RAND_CONV DIMINDEX_CONV THENC NUM_EXP_CONV) THENC
          NUM_LT_CONV) (lhand(concl th1)) in
        SYM(MP th1 (EQT_ELIM th2))
    | Comb(Comb(Const("+",_),_),_) ->
        let eth = BINOP_CONV conv tm in
        let mtm = rand(lhand(rand(concl eth)))
        and ntm = rand(rand(rand(concl eth))) in
        let mty = dest_word_ty(type_of mtm)
        and nty = dest_word_ty(type_of ntm) in
        let pty = max_num mty nty +/ num_1 in
        let th = INST_TYPE
          [mk_finty mty,m_ty; mk_finty nty,n_ty; mk_finty pty,p_ty] pth_add in
        let ath = (BINOP_CONV (BINOP_CONV DIMINDEX_CONV THENC NUM_LT_CONV))
                  (lhand(concl th)) in
        TRANS eth (SPECL [mtm; ntm] (MP th (EQT_ELIM (TRANS ath and_th))))
    | Comb(Comb(Const("*",_),_),_) ->
        let eth = BINOP_CONV conv tm in
        let mtm = rand(lhand(rand(concl eth)))
        and ntm = rand(rand(rand(concl eth))) in
        let mty = dest_word_ty(type_of mtm)
        and nty = dest_word_ty(type_of ntm) in
        let pty = mty +/ nty in
        let th = INST_TYPE
          [mk_finty mty,m_ty; mk_finty nty,n_ty; mk_finty pty,p_ty] pth_mul in
        let ath = (BINOP2_CONV (BINOP_CONV DIMINDEX_CONV THENC NUM_ADD_CONV)
                               DIMINDEX_CONV THENC
                   NUM_LE_CONV) (lhand(concl th)) in
        TRANS eth (SPECL [mtm; ntm] (MP th (EQT_ELIM ath)))
    | _ -> failwith "WORDIFY_CONV" in
  let fullconv = conv THENC GEN_REWRITE_CONV DEPTH_CONV [WORD_ZX_TRIVIAL] in
  fun tm -> if type_of tm = num_ty then fullconv tm
            else failwith "WORDIFY_CONV";;

let VAL_WORD_ADJUST_CONV =
  let m_ty = `:M` and n_ty = `:N`
  and pth = prove
   (`dimindex(:M) <= dimindex(:N)
     ==> !x. val(x:M word) = val(word_zx x:N word)`,
    SIMP_TAC[VAL_WORD_ZX]) in
  fun n tm ->
    match tm with
      Comb(Const("val",_),_) ->
       let m = dest_word_ty(type_of(rand tm)) in
       if m =/ n then REFL tm
       else if m >/ n then failwith "VAL_WORD_ADJUST_CONV: too small" else
       let th = INST_TYPE[mk_finty m,m_ty; mk_finty n,n_ty] pth in
       let cth = (BINOP_CONV DIMINDEX_CONV THENC NUM_LE_CONV)
                 (lhand(concl th)) in
      SPEC (rand tm) (MP th (EQT_ELIM cth))
   | _ -> failwith "VAL_WORD_ADJUST_CONV: wrong form of term";;

let VAL_WORD_ADJUST_BINOP_CONV tm =
  let tm1 = lhand tm and tm2 = rand tm in
  let n = max_num (dest_word_ty(type_of(rand tm1)))
                  (dest_word_ty(type_of(rand tm2))) in
  BINOP_CONV (VAL_WORD_ADJUST_CONV n) tm;;

let WORDIFY_ATOM_CONV =
  let num_ty = `:num`
  and pth = prove
   (`!(x:N word) (y:N word).
          val x < val y <=>
          (~bit (dimindex(:N)-1) x /\ bit (dimindex(:N)-1) y) \/
          (~bit (dimindex(:N)-1) x \/ bit (dimindex(:N)-1) y) /\
          bit (dimindex(:N)-1) (word_sub x y)`,
    CONV_TAC WORD_ARITH) in
  let pat =
      mk_abs(`x:num`,
             subst[`x:num`,`dimindex(:N)-1`]
               (rand(snd(strip_forall(concl pth))))) in
  let VAL_LT_CONV =
     GEN_REWRITE_CONV I [pth] THENC
     PAT_CONV pat (LAND_CONV DIMINDEX_CONV THENC NUM_SUB_CONV) in
  let conv tm =
    match tm with
      Comb(Comb(Const("=",_),_),t) when type_of t = num_ty ->
         (BINOP_CONV WORDIFY_CONV THENC
          VAL_WORD_ADJUST_BINOP_CONV THENC
          GEN_REWRITE_CONV I [VAL_EQ]) tm
    | Comb(Comb(Const("<",_),_),_) ->
         (BINOP_CONV WORDIFY_CONV THENC
          VAL_WORD_ADJUST_BINOP_CONV THENC
          VAL_LT_CONV) tm
    | Comb(Comb(Const(">",_),_),_) ->
         (BINOP_CONV WORDIFY_CONV THENC
          VAL_WORD_ADJUST_BINOP_CONV THENC
          GEN_REWRITE_CONV I [GT] THENC
          VAL_LT_CONV) tm
    | Comb(Comb(Const("<=",_),_),_) ->
         (BINOP_CONV WORDIFY_CONV THENC
          VAL_WORD_ADJUST_BINOP_CONV THENC
          GEN_REWRITE_CONV I [GSYM NOT_LT] THENC
          RAND_CONV VAL_LT_CONV) tm
    | Comb(Comb(Const(">=",_),_),_) ->
         (BINOP_CONV WORDIFY_CONV THENC
          VAL_WORD_ADJUST_BINOP_CONV THENC
          GEN_REWRITE_CONV I [GE] THENC
          GEN_REWRITE_CONV I [GSYM NOT_LT] THENC
          RAND_CONV VAL_LT_CONV) tm
    | _ -> failwith "WORDIFY_ATOM_CONV" in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Completely analogous functions for integer terms and comparison atoms.    *)
(* ------------------------------------------------------------------------- *)

let IWORDIFY_CONV =
  let m_ty = `:M` and n_ty = `:N` and p_ty = `:P` and int_ty = `:int`
  and and_th = TAUT `T /\ T <=> T`
  and pth_bitval = prove
   (`!b. &(bitval b) = ival(word(bitval b):2 word)`,
    REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV)
  and pth_val = prove
   (`dimindex(:N) < dimindex(:P)
     ==> !x. &(val(x:N word)) = ival(word_zx x:P word)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[IVAL_VAL; BIT_WORD_ZX] THEN
    ASM_SIMP_TAC[BIT_TRIVIAL; ARITH_RULE `n < p ==> n <= p - 1`] THEN
    ASM_SIMP_TAC[VAL_WORD_ZX; LT_IMP_LE; BITVAL_CLAUSES] THEN
    INT_ARITH_TAC)
  and pth_add = prove
   (`dimindex(:M) < dimindex(:P) /\ dimindex(:N) < dimindex(:P)
     ==> !x y. ival(x:M word) + ival(y:N word) =
               ival(word_add (word_sx x) (word_sx y):P word)`,
    REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS
     `ival((word_sx:M word->P word) x) +
      ival((word_sx:N word->P word) y)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[IVAL_WORD_SX; LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC INT_CONG_IMP_EQ THEN
    EXISTS_TAC `(&2:int) pow dimindex(:P)` THEN
    ONCE_REWRITE_TAC[INTEGER_RULE
     `(x:int == y) (mod p) <=> (y == x) (mod p)`] THEN
    REWRITE_TAC[ICONG_WORD_ADD] THEN ASM_SIMP_TAC[IVAL_WORD_SX; LT_IMP_LE] THEN
    MAP_EVERY (MP_TAC o C ISPEC IVAL_BOUND)
     [`word_add (word_sx(x:M word)) (word_sx(y:N word)):P word`;
      `y:N word`; `x:M word`] THEN
    MATCH_MP_TAC(INT_ARITH
     `&2 * a <= c /\ &2 * b <= c /\ &2 * c <= e
      ==> --a <= x /\ x < a ==> --b <= y /\ y < b ==> --c <= z /\ z < c
          ==> abs((x + y) - z):int < e`) THEN
    REWRITE_TAC[GSYM(CONJUNCT2 INT_POW)] THEN
    SUBGOAL_THEN `~(dimindex(:M) = 0) /\ ~(dimindex(:N) = 0)`
    STRIP_ASSUME_TAC THENL [REWRITE_TAC[DIMINDEX_NONZERO]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_POW_MONO THEN ASM_ARITH_TAC)
  and pth_sub = prove
   (`dimindex(:M) < dimindex(:P) /\ dimindex(:N) < dimindex(:P)
     ==> !x y. ival(x:M word) - ival(y:N word) =
               ival(word_sub (word_sx x) (word_sx y):P word)`,
    REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS
     `ival((word_sx:M word->P word) x) -
      ival((word_sx:N word->P word) y)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[IVAL_WORD_SX; LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC INT_CONG_IMP_EQ THEN
    EXISTS_TAC `(&2:int) pow dimindex(:P)` THEN
    ONCE_REWRITE_TAC[INTEGER_RULE
     `(x:int == y) (mod p) <=> (y == x) (mod p)`] THEN
    REWRITE_TAC[ICONG_WORD_SUB] THEN ASM_SIMP_TAC[IVAL_WORD_SX; LT_IMP_LE] THEN
    MAP_EVERY (MP_TAC o C ISPEC IVAL_BOUND)
     [`word_sub (word_sx(x:M word)) (word_sx(y:N word)):P word`;
      `y:N word`; `x:M word`] THEN
    MATCH_MP_TAC(INT_ARITH
     `&2 * a <= c /\ &2 * b <= c /\ &2 * c <= e
      ==> --a <= x /\ x < a ==> --b <= y /\ y < b ==> --c <= z /\ z < c
          ==> abs((x - y) - z):int < e`) THEN
    REWRITE_TAC[GSYM(CONJUNCT2 INT_POW)] THEN
    SUBGOAL_THEN `~(dimindex(:M) = 0) /\ ~(dimindex(:N) = 0)`
    STRIP_ASSUME_TAC THENL [REWRITE_TAC[DIMINDEX_NONZERO]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_POW_MONO THEN ASM_ARITH_TAC)
  and pth_neg = prove
   (`dimindex(:N) < dimindex(:P)
     ==> !x. --(ival(x:N word)) = ival(word_neg(word_sx x:P word))`,
    REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS
     `--ival((word_sx:N word->P word) x)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[IVAL_WORD_SX; LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC INT_CONG_IMP_EQ THEN
    EXISTS_TAC `(&2:int) pow dimindex(:P)` THEN
    ONCE_REWRITE_TAC[INTEGER_RULE
     `(x:int == y) (mod p) <=> (y == x) (mod p)`] THEN
    REWRITE_TAC[ICONG_WORD_NEG] THEN ASM_SIMP_TAC[IVAL_WORD_SX; LT_IMP_LE] THEN
    MAP_EVERY (MP_TAC o C ISPEC IVAL_BOUND)
     [`word_neg (word_sx(x:N word)):P word`; `x:N word`] THEN
    MATCH_MP_TAC(INT_ARITH
     `&2 * a <= c /\ &2 * c <= e
      ==> --a <= x /\ x < a ==> --c <= z /\ z < c
          ==> abs(--x - z):int < e`) THEN
    REWRITE_TAC[GSYM(CONJUNCT2 INT_POW)] THEN
    SUBGOAL_THEN `~(dimindex(:M) = 0) /\ ~(dimindex(:N) = 0)`
    STRIP_ASSUME_TAC THENL [REWRITE_TAC[DIMINDEX_NONZERO]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_POW_MONO THEN ASM_ARITH_TAC)
  and pth_mul = prove
   (`dimindex(:M) + dimindex(:N) <= dimindex(:P)
     ==> !x y. ival(x:M word) * ival(y:N word) =
               ival(word_mul (word_sx x) (word_sx y):P word)`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~(dimindex(:M) = 0) /\ ~(dimindex(:N) = 0)`
    STRIP_ASSUME_TAC THENL [REWRITE_TAC[DIMINDEX_NONZERO]; ALL_TAC] THEN
    SUBGOAL_THEN `dimindex(:M) < dimindex(:P) /\ dimindex(:N) < dimindex(:P)`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `ival((word_sx:M word->P word) x) *
      ival((word_sx:N word->P word) y)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[IVAL_WORD_SX; LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC INT_CONG_IMP_EQ THEN
    EXISTS_TAC `(&2:int) pow dimindex(:P)` THEN
    ONCE_REWRITE_TAC[INTEGER_RULE
     `(x:int == y) (mod p) <=> (y == x) (mod p)`] THEN
    REWRITE_TAC[ICONG_WORD_MUL] THEN ASM_SIMP_TAC[IVAL_WORD_SX; LT_IMP_LE] THEN
    MP_TAC(ISPEC `word_mul (word_sx(x:M word)) (word_sx(y:N word)):P word`
        IVAL_BOUND) THEN
    MATCH_MP_TAC(INT_ARITH
     `&2 * c <= e /\ &2 * abs(xy) <= c
      ==> --c <= z /\ z < c
          ==> abs(xy - z):int < e`) THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC
       `(&2:int) * &2 pow (dimindex(:M) - 1) * &2 pow (dimindex(:N) - 1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC INT_LE_MUL2 THEN
        REWRITE_TAC[INT_ABS_POS; INT_LE_REFL; INT_POS; INT_ABS_MUL] THEN
        MATCH_MP_TAC INT_LE_MUL2 THEN
        REWRITE_TAC[INT_ABS_POS; INT_LE_REFL; INT_POS; INT_ABS_MUL] THEN
        CONJ_TAC THEN MATCH_MP_TAC(INT_ARITH
         `--e:int <= x /\ x < e ==> abs(x) <= e`) THEN
        REWRITE_TAC[IVAL_BOUND];
        ALL_TAC]] THEN
    REWRITE_TAC[GSYM INT_POW; GSYM INT_POW_ADD] THEN
    MATCH_MP_TAC INT_POW_MONO THEN ASM_ARITH_TAC) in
  let log2 =
    let rec log2 n m i =
      if n </ m then i else log2 n (num_2 */ m) (i + 1) in
    fun n -> num(log2 (abs_num n) num_1 0) in
  let ilog2 =
    let rec ilog2 n m i =
      if minus_num m <=/ n && n </ m then i
      else ilog2 n (num_2 */ m) (i + 1) in
    fun n -> num(ilog2 n num_1 1) in
  let rec conv tm =
    if is_intconst tm then
       let x = dest_intconst tm in
       let n = ilog2 x in
       let x' = mod_num x (power_num num_2 n) in
       let tyin = [mk_finty n,n_ty] in
       SYM(WORD_IVAL_CONV
         (mk_comb(mk_const("ival",tyin),
               mk_comb(mk_const("word",tyin),mk_numeral x'))))
    else match tm with
      Comb(Const("int_of_num",_),Comb(Const("bitval",_),_)) ->
          GEN_REWRITE_CONV I [pth_bitval] tm
    | Comb(Const("ival",_),_) -> REFL tm
    | Comb(Const("int_of_num",_),Comb(Const("val",_),ntm)) ->
        let nty = dest_word_ty(type_of ntm) in
        let pty = nty +/ num_1 in
        let th = INST_TYPE
          [mk_finty nty,n_ty; mk_finty pty,p_ty] pth_val in
        let ath = (BINOP_CONV DIMINDEX_CONV THENC NUM_LT_CONV)
                  (lhand(concl th)) in
        SPEC ntm (MP th (EQT_ELIM ath))
    | Comb(Const("int_neg",_),_) ->
        let eth = RAND_CONV conv tm in
        let ntm = rand(rand(rand(concl eth))) in
        let nty = dest_word_ty(type_of ntm) in
        let pty = nty +/ num_1 in
        let th = INST_TYPE[mk_finty nty,n_ty; mk_finty pty,p_ty] pth_neg in
        let ath = (BINOP_CONV DIMINDEX_CONV THENC NUM_LT_CONV)
                  (lhand(concl th)) in
        TRANS eth (SPEC ntm (MP th (EQT_ELIM ath)))
    | Comb(Comb(Const("int_add",_),_),_) ->
        let eth = BINOP_CONV conv tm in
        let mtm = rand(lhand(rand(concl eth)))
        and ntm = rand(rand(rand(concl eth))) in
        let mty = dest_word_ty(type_of mtm)
        and nty = dest_word_ty(type_of ntm) in
        let pty = max_num mty nty +/ num_1 in
        let th = INST_TYPE
          [mk_finty mty,m_ty; mk_finty nty,n_ty; mk_finty pty,p_ty] pth_add in
        let ath = (BINOP_CONV (BINOP_CONV DIMINDEX_CONV THENC NUM_LT_CONV))
                  (lhand(concl th)) in
        TRANS eth (SPECL [mtm; ntm] (MP th (EQT_ELIM (TRANS ath and_th))))
    | Comb(Comb(Const("int_sub",_),_),_) ->
        let eth = BINOP_CONV conv tm in
        let mtm = rand(lhand(rand(concl eth)))
        and ntm = rand(rand(rand(concl eth))) in
        let mty = dest_word_ty(type_of mtm)
        and nty = dest_word_ty(type_of ntm) in
        let pty = max_num mty nty +/ num_1 in
        let th = INST_TYPE
          [mk_finty mty,m_ty; mk_finty nty,n_ty; mk_finty pty,p_ty] pth_sub in
        let ath = (BINOP_CONV (BINOP_CONV DIMINDEX_CONV THENC NUM_LT_CONV))
                  (lhand(concl th)) in
        TRANS eth (SPECL [mtm; ntm] (MP th (EQT_ELIM (TRANS ath and_th))))
    | Comb(Comb(Const("int_mul",_),_),_) ->
        let eth = BINOP_CONV conv tm in
        let mtm = rand(lhand(rand(concl eth)))
        and ntm = rand(rand(rand(concl eth))) in
        let mty = dest_word_ty(type_of mtm)
        and nty = dest_word_ty(type_of ntm) in
        let pty = mty +/ nty in
        let th = INST_TYPE
          [mk_finty mty,m_ty; mk_finty nty,n_ty; mk_finty pty,p_ty] pth_mul in
        let ath = (BINOP2_CONV (BINOP_CONV DIMINDEX_CONV THENC NUM_ADD_CONV)
                               DIMINDEX_CONV THENC
                   NUM_LE_CONV) (lhand(concl th)) in
        TRANS eth (SPECL [mtm; ntm] (MP th (EQT_ELIM ath)))
    | _ -> failwith "IWORDIFY_CONV" in
  let fullconv = conv THENC GEN_REWRITE_CONV DEPTH_CONV [WORD_SX_TRIVIAL] in
  fun tm -> if type_of tm = int_ty then fullconv tm
            else failwith "IWORDIFY_CONV";;

let IVAL_WORD_ADJUST_CONV =
  let m_ty = `:M` and n_ty = `:N`
  and pth = prove
   (`dimindex(:M) <= dimindex(:N)
     ==> !x. ival(x:M word) = ival(word_sx x:N word)`,
    SIMP_TAC[IVAL_WORD_SX]) in
  fun n tm ->
    match tm with
      Comb(Const("ival",_),_) ->
       let m = dest_word_ty(type_of(rand tm)) in
       if m =/ n then REFL tm
       else if m >/ n then failwith "IVAL_WORD_ADJUST_CONV: too small" else
       let th = INST_TYPE[mk_finty m,m_ty; mk_finty n,n_ty] pth in
       let cth = (BINOP_CONV DIMINDEX_CONV THENC NUM_LE_CONV)
                 (lhand(concl th)) in
      SPEC (rand tm) (MP th (EQT_ELIM cth))
   | _ -> failwith "IVAL_WORD_ADJUST_CONV: wrong form of term";;

let IVAL_WORD_ADJUST_BINOP_CONV tm =
  let tm1 = lhand tm and tm2 = rand tm in
  let n = max_num (dest_word_ty(type_of(rand tm1)))
                  (dest_word_ty(type_of(rand tm2))) in
  BINOP_CONV (IVAL_WORD_ADJUST_CONV n) tm;;

let IWORDIFY_ATOM_CONV =
  let int_ty = `:int`
  and pth = prove
   (`!(x:N word) (y:N word).
          ival x < ival y <=>
          (bit (dimindex(:N)-1) x /\ ~bit (dimindex(:N)-1) y) \/
           (bit (dimindex(:N)-1) x \/ ~bit (dimindex(:N)-1) y) /\
          bit (dimindex(:N)-1) (word_sub x y)`,
    CONV_TAC WORD_ARITH) in
  let pat =
      mk_abs(`x:num`,
             subst[`x:num`,`dimindex(:N)-1`]
               (rand(snd(strip_forall(concl pth))))) in
  let IVAL_LT_CONV =
     GEN_REWRITE_CONV I [pth] THENC
     PAT_CONV pat (LAND_CONV DIMINDEX_CONV THENC NUM_SUB_CONV) in
  let conv tm =
    match tm with
      Comb(Comb(Const("=",_),_),t) when type_of t = int_ty ->
         (BINOP_CONV IWORDIFY_CONV THENC
          IVAL_WORD_ADJUST_BINOP_CONV THENC
          GEN_REWRITE_CONV I [IVAL_EQ]) tm
    | Comb(Comb(Const("int_lt",_),_),_) ->
         (BINOP_CONV IWORDIFY_CONV THENC
          IVAL_WORD_ADJUST_BINOP_CONV THENC
          IVAL_LT_CONV) tm
    | Comb(Comb(Const("int_gt",_),_),_) ->
         (BINOP_CONV IWORDIFY_CONV THENC
          IVAL_WORD_ADJUST_BINOP_CONV THENC
          GEN_REWRITE_CONV I [INT_GT] THENC
          IVAL_LT_CONV) tm
    | Comb(Comb(Const("int_le",_),_),_) ->
         (BINOP_CONV IWORDIFY_CONV THENC
          IVAL_WORD_ADJUST_BINOP_CONV THENC
          GEN_REWRITE_CONV I [GSYM INT_NOT_LT] THENC
          RAND_CONV IVAL_LT_CONV) tm
    | Comb(Comb(Const("int_ge",_),_),_) ->
         (BINOP_CONV IWORDIFY_CONV THENC
          IVAL_WORD_ADJUST_BINOP_CONV THENC
          GEN_REWRITE_CONV I [INT_GE] THENC
          GEN_REWRITE_CONV I [GSYM INT_NOT_LT] THENC
          RAND_CONV IVAL_LT_CONV) tm
    | _ -> failwith "IWORDIFY_ATOM_CONV" in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Convert a word(....) term with composite inside to word form.             *)
(* ------------------------------------------------------------------------- *)

let WORDIFY_WORD_CONV =
  let conv =
    RAND_CONV WORDIFY_CONV THENC
    (GEN_REWRITE_CONV I [WORD_VAL] ORELSEC
     GEN_REWRITE_CONV I [GSYM word_zx]) in
  fun tm ->
    match tm with
      Comb(Const("word",_),t) when not(is_numeral t) -> conv tm
    | _ -> failwith "WORDIFY_WORD_CONV";;

(* ------------------------------------------------------------------------- *)
(* Expanding multiplication, popcount and unsigned word ordering relations.  *)
(* ------------------------------------------------------------------------- *)

let WORD_MUL_EXPAND_CONV =
  let pth = prove
   (`!b x:N word.
          word(bitval b * val x) =
          word_and (word_neg(word(bitval b))) x`,
    REPEAT GEN_TAC THEN REWRITE_TAC[WORD_AND_MASK] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES; WORD_VAL]) in
  let conv =
    GEN_REWRITE_CONV I [REWRITE_RULE[NUMSEG_LT_DIMINDEX] WORD_MUL_EXPAND] THENC
    RAND_CONV
     (LAND_CONV(RAND_CONV(LAND_CONV DIMINDEX_CONV THENC NUM_SUB_CONV)) THENC
      EXPAND_NSUM_BALANCE_CONV) THENC
    ONCE_DEPTH_CONV BIT_WORD_CONV THENC
    GEN_REWRITE_CONV DEPTH_CONV
     [BITVAL_CLAUSES; MULT_CLAUSES; ADD_CLAUSES] THENC
    GEN_REWRITE_CONV TOP_SWEEP_CONV [WORD_ADD] THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [WORD_VAL; pth]
  and swap = GEN_REWRITE_CONV I [WORD_MUL_SYM] in
  fun tm ->
    match tm with
      Comb(Comb(Const("word_mul",_),_),Comb(Const("word",_),n))
      when is_numeral n -> (swap THENC conv) tm
    | Comb(Comb(Const("word_mul",_),Comb(Const("word",_),n)),_)
      when is_numeral n -> conv tm
    | Comb(Comb(Const("word_mul",_),x),y) -> conv tm
    | _ -> failwith "WORD_MUL_EXPAND_CONV";;

let WORD_POPCOUNT_EXPAND_CONV =
  GEN_REWRITE_CONV I
   [REWRITE_RULE[NUMSEG_LT_DIMINDEX] WORD_POPCOUNT_NSUM] THENC
  LAND_CONV (RAND_CONV(LAND_CONV DIMINDEX_CONV THENC NUM_SUB_CONV)) THENC
  EXPAND_NSUM_BALANCE_CONV;;

let WORD_INEQ_RELATION_EXPAND_CONV =
  GEN_REWRITE_CONV I
   (map (REWRITE_CONV[relational2; word_ule; word_ult; word_uge; word_ugt;
                      irelational2; word_ile; word_ilt; word_ige; word_igt])
        [`word_ule (x:N word) y`; `word_ult (x:N word) y`;
         `word_uge (x:N word) y`; `word_ugt (x:N word) y`;
         `word_ile (x:N word) y`; `word_ilt (x:N word) y`;
         `word_ige (x:N word) y`; `word_igt (x:N word) y`]);;

(* ------------------------------------------------------------------------- *)
(* Basic bit-blasting tactic.                                                *)
(* ------------------------------------------------------------------------- *)

let VAL_MOD_OR_DIV_CONV =
  let conv_div = GEN_REWRITE_CONV I [GSYM VAL_WORD_USHR]
  and conv_mod =
    RAND_CONV EMPOWER_CONV THENC
    GEN_REWRITE_CONV I [GSYM VAL_WORD_AND_MASK_WORD] THENC
    funpow 3 RAND_CONV (LAND_CONV NUM_EXP_CONV THENC NUM_SUB_CONV) in
  fun tm ->
    match tm with
      Comb(Comb(Const("DIV",_),Comb(Const("val",_),_)),n) -> conv_div tm
    | Comb(Comb(Const("MOD",_),Comb(Const("val",_),_)),n) -> conv_mod tm
    | _ -> failwith "VAL_MOD_OR_DIV_CONV";;

let BITBLAST_THEN =
  let carrying tm =
    match tm with
      Comb(Comb(Const("word_add",_),_),_) -> true
    | Comb(Comb(Const("word_sub",_),_),_) -> true
    | Comb(Const("word_neg",_),
           Comb(Const("word",_),
                Comb(Const("bitval",_),_))) -> false
    | Comb(Const("word_neg",_),_) -> true
    | _ -> false
  and BITWISE_EXPAND_CONV =
    GEN_REWRITE_CONV I [WORD_EQ_BITS_ALT] THENC
    BINDER_CONV(LAND_CONV(RAND_CONV(!word_SIZE_CONV))) THENC
    EXPAND_CASES_CONV in
  let BITBLAST_EQUATION th =
    let ths = CONJUNCTS(CONV_RULE BITWISE_EXPAND_CONV th) in
    end_itlist CONJ (map (CONV_RULE
     (LAND_CONV
       (BIT_WORD_CONV THENC SUBS_CONV[th] THENC
        TOP_DEPTH_CONV (BIT_WORD_CONV o check (not o carrying o rand))) THENC
      SYM_CONV THENC
      RAND_CONV(REWRITE_CONV[]))) ths) in
  let wordbits =
    let bit_tm = `bit:num->(N)word->bool` and n_ty = `:N` in
    let wordbits_var tm =
      try let ty = type_of tm in
          let n = dest_word_ty ty in
          let btm = inst[mk_finty n,n_ty] bit_tm in
          map (fun i -> mk_comb(mk_comb(btm,mk_small_numeral i),tm))
              (0--(Num.int_of_num n-1))
      with Failure _ -> [] in
    let rec interleave lis =
      match lis with
        [] -> []
      | []::rst -> interleave rst
      | (h::t)::rst -> h::(interleave(rst @ [t])) in
    fun tm -> interleave (map wordbits_var (frees tm)) in
  fun tac ->
    REPEAT(GEN_TAC ORELSE CONJ_TAC) THEN
    REPEAT((COND_CASES_TAC THEN POP_ASSUM MP_TAC) ORELSE
           (CHANGED_TAC(CONV_TAC(ONCE_DEPTH_CONV let_CONV)))) THEN
    W(fun (_,w) -> let vars = wordbits w in
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[word_UINT_MAX; WORD_INT_MIN; WORD_INT_MAX] THEN
      CONV_TAC(DEPTH_CONV
       (WORD_RED_CONV ORELSEC NUM_RED_CONV ORELSEC DIMINDEX_CONV)) THEN
      CONV_TAC(ONCE_DEPTH_CONV WORD_INEQ_RELATION_EXPAND_CONV) THEN
      GEN_REWRITE_TAC TOP_DEPTH_CONV
       [WORD_ODDPARITY_POPCOUNT; WORD_EVENPARITY_POPCOUNT;
        WORD_CTZ_EMULATION_POPCOUNT; GSYM WORD_CTZ_REVERSEFIELDS] THEN
      CONV_TAC(ONCE_DEPTH_CONV WORD_POPCOUNT_EXPAND_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV WORDIFY_WORD_CONV) THEN
      CONV_TAC(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV)) THEN
      CONV_TAC(ONCE_DEPTH_CONV VAL_MOD_OR_DIV_CONV) THEN
      CONV_TAC(DEPTH_CONV
       (WORDIFY_ATOM_CONV ORELSEC IWORDIFY_ATOM_CONV)) THEN
      CONV_TAC(DEPTH_CONV WORD_MUL_EXPAND_CONV) THEN
      REPEAT(W(fun (_,w) ->
        let t = hd(sort free_in (find_terms carrying w)) in
        let v = genvar(type_of t) in
         ABBREV_TAC(mk_eq(v,t)))) THEN
      CONV_TAC(ONCE_DEPTH_CONV
       (BITWISE_EXPAND_CONV THENC TOP_DEPTH_CONV BIT_WORD_CONV)) THEN
      CONV_TAC(TOP_DEPTH_CONV
       (BIT_WORD_CONV o check (not o carrying o rand))) THEN
      TRY(POP_ASSUM_LIST
       (MP_TAC o end_itlist CONJ o map BITBLAST_EQUATION o rev)) THEN
      REWRITE_TAC[] THEN tac vars);;

let BITBLAST_TAC = BITBLAST_THEN (CONV_TAC o BDD_DEFTAUT);;

let BITBLAST_RULE tm = time prove(tm,BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* SIMD repetition of a unary (usimd) or binary (simd) function.             *)
(* ------------------------------------------------------------------------- *)

let usimd2 = new_definition
 `(usimd2:(N word->M word)->((N)tybit0)word->((M)tybit0) word) f x =
    word_join (f (word_subword x (dimindex(:N),dimindex(:N))))
              (f (word_subword x (0,dimindex(:N))))`;;

let simd2 = new_definition
 `(simd2:(N word->N word->N word)->
        ((N)tybit0)word->((N)tybit0) word->((N)tybit0) word) f x y =
    word_join (f (word_subword x (dimindex(:N),dimindex(:N)))
                 (word_subword y (dimindex(:N),dimindex(:N))))
              (f (word_subword x (0,dimindex(:N)))
                 (word_subword y (0,dimindex(:N))))`;;

let usimd4 = new_definition
 `usimd4 (f:N word->M word) = usimd2 (usimd2 f)`;;

let simd4 = new_definition
 `simd4 (f:N word->N word->N word) = simd2 (simd2 f)`;;

let usimd8 = new_definition
 `usimd8 (f:N word->M word) = usimd2 (usimd4 f)`;;

let simd8 = new_definition
 `simd8 (f:N word->N word->N word) = simd2 (simd4 f)`;;

let usimd16 = new_definition
 `usimd16 (f:N word->M word) = usimd2 (usimd8 f)`;;

let simd16 = new_definition
 `simd16 (f:N word->N word->N word) = simd2 (simd8 f)`;;

let USIMD2 = prove
 (`!(f:N word->M word) xhi xlo.
        usimd2 f (word_join xhi xlo) = word_join (f xhi) (f xlo)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[usimd2] THEN BINOP_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_JOIN] THEN
  SIMP_TAC[ADD_CLAUSES; DIMINDEX_TYBIT0; ARITH_RULE `MIN x x = x`;
           ADD_SUB2; ARITH_RULE `i < n ==> i < 2 * n`;
           ARITH_RULE `n + i < 2 * n <=> i < n`;
           ARITH_RULE `~(n + i:num < n)`]);;

let SIMD2 = prove
 (`!(f:N word->N word->N word) xhi xlo yhi ylo.
        simd2 f (word_join xhi xlo) (word_join yhi ylo) =
        word_join (f xhi yhi) (f xlo ylo)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simd2] THEN BINOP_TAC THEN BINOP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_JOIN] THEN
  SIMP_TAC[ADD_CLAUSES; DIMINDEX_TYBIT0; ARITH_RULE `MIN x x = x`;
           ADD_SUB2; ARITH_RULE `i < n ==> i < 2 * n`;
           ARITH_RULE `n + i < 2 * n <=> i < n`;
           ARITH_RULE `~(n + i:num < n)`]);;
