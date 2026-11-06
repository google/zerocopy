(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Additions to Library/words.ml.                                            *)
(* ========================================================================= *)

let WORD_SUB2 = MESON [WORD_SUB]
  `y <= x ==> word_sub (word x) (word y):N word = word (x - y)`;;

(* ------------------------------------------------------------------------- *)
(* Conversionals returning iword instead of word                             *)
(* ------------------------------------------------------------------------- *)

let IWORD_SX_CONV =
  let pth = prove
   (`(word_sx:M word->N word) (word (NUMERAL n)) =
     iword(ival(word(NUMERAL n):M word))`,
    REWRITE_TAC[word_sx]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV WORD_IVAL_CONV;;

(* ------------------------------------------------------------------------- *)
(* Mappings between numbers and byte-lists (little-endian)                   *)
(* ------------------------------------------------------------------------- *)

let num_of_bytelist = define
 `(num_of_bytelist [] = 0) /\
  (!h t. num_of_bytelist (CONS h t) = val(h:byte) + 256 * num_of_bytelist t)`;;

let bytelist_of_num = define
 `(bytelist_of_num 0 n = []) /\
  (bytelist_of_num (SUC k) n =
     CONS (word(n MOD 256):byte) (bytelist_of_num k (n DIV 256)))`;;

let bytelist_of_int = define `bytelist_of_int k n =
  bytelist_of_num k (num_of_int (n rem &(256 EXP k)))`;;

let LENGTH_BYTELIST_OF_NUM = prove
 (`!k n. LENGTH(bytelist_of_num k n) = k`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[bytelist_of_num; LENGTH]);;

let LENGTH_BYTELIST_OF_INT = prove
 (`!k n. LENGTH(bytelist_of_int k n) = k`,
  REWRITE_TAC [bytelist_of_int; LENGTH_BYTELIST_OF_NUM]);;

let NUM_OF_BYTELIST_BOUND = prove
 (`!l. num_of_bytelist l < 256 EXP (LENGTH l)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[LENGTH; num_of_bytelist; ARITH; EXP] THEN
  X_GEN_TAC `h:byte` THEN MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

let BYTELIST_OF_NUM_OF_BYTELIST = prove
 (`!l. bytelist_of_num (LENGTH l) (num_of_bytelist l) = l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[num_of_bytelist; bytelist_of_num; LENGTH] THEN FIRST_X_ASSUM
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  SIMP_TAC[CONS_11; MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ; WORD_VAL_GALOIS] THEN
  REWRITE_TAC[DIMINDEX_8; MOD_EQ_SELF; ARITH; MOD_MOD_REFL] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
  SIMP_TAC[DIV_LT; ADD_CLAUSES] THEN MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

let NUM_OF_BYTELIST_OF_NUM_0 = prove
 (`!k. num_of_bytelist(bytelist_of_num k 0) = 0`,
  INDUCT_TAC THEN SIMP_TAC[num_of_bytelist; bytelist_of_num] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[VAL_WORD_0; ARITH]);;

let NUM_OF_BYTELIST_OF_NUM = prove
 (`!k n. num_of_bytelist(bytelist_of_num k n) = n MOD (256 EXP k)`,
  INDUCT_TAC THEN REWRITE_TAC[num_of_bytelist] THENL
   [REWRITE_TAC[bytelist_of_num; num_of_bytelist; EXP; MOD_1]; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN ASM_REWRITE_TAC[bytelist_of_num; num_of_bytelist] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8; ARITH; MOD_MOD_REFL] THEN
  REWRITE_TAC[EXP; MOD_MULT_MOD] THEN ARITH_TAC);;

let BYTELIST_OF_NUM_MOD = prove
 (`!k n. bytelist_of_num k (n MOD (256 EXP k)) = bytelist_of_num k n`,
  REPEAT GEN_TAC THEN REWRITE_TAC [GSYM NUM_OF_BYTELIST_OF_NUM] THEN
  REWRITE_TAC [REWRITE_RULE [LENGTH_BYTELIST_OF_NUM]
    (SPEC `bytelist_of_num k n` BYTELIST_OF_NUM_OF_BYTELIST)]);;

let NUM_OF_BYTELIST_OF_NUM_EQ = prove
 (`!k n. n < 256 EXP k ==> num_of_bytelist(bytelist_of_num k n) = n`,
  SIMP_TAC[NUM_OF_BYTELIST_OF_NUM; MOD_LT]);;

let BYTELIST_OF_INT_OF_NUM = prove
 (`bytelist_of_int k (&n) = bytelist_of_num k n`,
  REWRITE_TAC [bytelist_of_int; INT_OF_NUM_REM; NUM_OF_INT_OF_NUM;
   BYTELIST_OF_NUM_MOD]);;

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
(* Reading words from bytelists.                                             *)
(* ------------------------------------------------------------------------- *)

let read_word_n = define
  `(!l. read_word_n 0 l = SOME(0,l)) /\
   (!n. read_word_n (SUC n) [] = NONE) /\
   (!n b l. read_word_n (SUC n) (CONS (b:byte) l) =
    read_word_n n l >>= \(r,l).
    SOME(val b + 2 EXP 8 * r,l))`;;

let read_word = new_definition `read_word n l =
  read_word_n n l >>= \(r,l). SOME(word r:N word,l)`;;

let read_byte = new_definition
  `read_byte = read_word 1: byte list -> (byte # byte list) option`
and read_int16 = new_definition
  `read_int16 = read_word 2: byte list -> (int16 # byte list) option`
and read_int32 = new_definition
  `read_int32 = read_word 4: byte list -> (int32 # byte list) option`
and read_int64 = new_definition
  `read_int64 = read_word 8: byte list -> (int64 # byte list) option`;;

let read_byte_val = prove
 (`read_byte [] = NONE /\ !a l. read_byte (CONS a l) = SOME (a, l)`,
  REWRITE_TAC [read_byte; read_word; ONE;
    read_word_n; obind; MULT_0; ADD_0; WORD_VAL]);;

let read_word_n_eq_some = prove
 (`read_word_n n l = SOME (a, l') <=>
   ?l1. l = APPEND l1 l' /\ LENGTH l1 = n /\ a = num_of_bytelist l1`,
  SPECL_TAC [`n:num`; `l:byte list`; `a:num`] THEN INDUCT_TAC THEN
  REWRITE_TAC [read_word_n] THENL
   [REWRITE_TAC [OPTION_INJ; PAIR_EQ; LENGTH_EQ_NIL] THEN
    CONV_TAC (ONCE_DEPTH_CONV UNWIND_CONV) THEN
    REWRITE_TAC [APPEND; num_of_bytelist] THEN METIS_TAC []; ALL_TAC] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC [read_word_n] THENL
   [REWRITE_TAC [OPTION_DISTINCT; APPEND_EQ_NIL] THEN REPEAT STRIP_TAC THEN
    (POP_ASSUM o K o POP_ASSUM) (fun th1 -> POP_ASSUM (fun th2 ->
      MP_TAC (REWRITE_RULE
        [LENGTH; REWRITE_RULE [APPEND_EQ_NIL] (SYM th2)] th1) THEN
      ARITH_TAC));
    REWRITE_TAC [obind_eq_some; EXISTS_PAIR_THM; OPTION_INJ; PAIR_EQ] THEN
    GEN_TAC THEN CONV_TAC (ONCE_DEPTH_CONV UNWIND_CONV) THEN
    (POP_ASSUM o K o POP_ASSUM) (fun th -> REWRITE_TAC [th;
      LENGTH_EQ_CONS; LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM]) THEN
    CONV_TAC (ONCE_DEPTH_CONV UNWIND_CONV) THEN
    REWRITE_TAC [APPEND; CONS_11; num_of_bytelist] THEN
    CONV_TAC (ONCE_DEPTH_CONV UNWIND_CONV THENC NUM_REDUCE_CONV) THEN
    METIS_TAC []]);;

let read_word_eq_some = prove
 (`read_word n l = SOME (a, l') <=>
   ?l1. l = APPEND l1 l' /\ LENGTH l1 = n /\ a = word (num_of_bytelist l1)`,
  REWRITE_TAC [read_word; obind_eq_some; EXISTS_PAIR_THM; OPTION_INJ;
    PAIR_EQ; read_word_n_eq_some; LEFT_AND_EXISTS_THM] THEN
  CONV_TAC (ONCE_DEPTH_CONV UNWIND_CONV) THEN
  PURE_REWRITE_TAC [EQ_SYM_EQ] THEN REFL_TAC);;

let READ_WORD_CONV =
  let pth1 = prove
   (`read_word_n 1 (CONS (word a0) l) = SOME (a0 MOD 2 EXP (8 * 1), l)`,
    REWRITE_TAC [ONE; read_word_n; obind;
      VAL_WORD; ADD_CLAUSES; MULT_CLAUSES] THEN
    CONV_TAC (ONCE_DEPTH_CONV DIMINDEX_CONV) THEN REFL_TAC)
  and pthS =
    let pth = prove
     (`num_shift_add a r 8 = r2 ==>
       read_word_n n l = SOME (r, l2) ==>
       read_word_n (SUC n) (CONS (word a) l) = SOME (r2, l2)`,
      DISCH_THEN (SUBST1_TAC o SYM) THEN DISCH_THEN (fun th -> REWRITE_TAC [
        ADD1; read_word_n; th; obind; num_shift_add; VAL_WORD; MULT_SYM]) THEN
      CONV_TAC (ONCE_DEPTH_CONV DIMINDEX_CONV) THEN REFL_TAC) in
    (UNDISCH_ALL o prove)
      (`num_shift_add a r 8 = r2 ==>
        read_word_n n l = SOME (r MOD (2 EXP (8 * n)), l2) ==>
        read_word_n (SUC n) (CONS (word a) l) =
          SOME (r2 MOD (2 EXP (8 * SUC n)), l2)`,
       DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC pth THEN
       REWRITE_TAC [MULT_SUC; EXP_ADD; MULT_SYM; num_shift_add_mod] THEN
       ALL_TAC)
  and pthc = prove
   (`m = n ==> f = read_word n ==> dimindex(:N) = w ==>
     read_word_n m l = SOME (r MOD 2 EXP w, l2) ==>
     f l = SOME ((word r: N word), l2)`,
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    DISCH_THEN (fun th -> REWRITE_TAC [read_word; th; obind; WORD_MOD_SIZE]))
  and ai = Array.init 8 (fun i -> mk_var("a"^string_of_int i, `:num`))
  and ri = Array.init 8 (fun i -> mk_var("r"^string_of_int i, `:num`))
  and ea,eai,el,er = `a:num`,`a:int`,`l:byte list`,`r:num` in
  let pthi1 = SPECL [`word a0:byte`; el] (CONJUNCT2 read_byte_val)
  and pthi2,pthi4,pthi8 =
    let rec mk_pth n =
      if n = 1 then [pth1] else
      let n' = n - 1 in
      let ls = mk_pth n' in let th1 = hd ls in
      let l,r = dest_eq (concl th1) in
      let en = lhand l and l = rand l and r = rand r in
      let l2 = rand r and r = lhand (lhand r) in
      let th2 = INST [ai.(n'),`a:num`; r,`r:num`; ri.(n'),`r2:num`;
        l,el; l2,`l2:byte list`; en,`n:num`] pthS in
      PROVE_HYP th1 th2 :: ls in
    let cleanup dth pth =
      let m,w = (lhand F_F (rand o rand o lhand o rand))
        (dest_eq (concl pth)) in
      let th = MATCH_MP (MATCH_MP pthc (NUM_REDUCE_CONV m)) dth in
      let th = MATCH_MP th (TRANS
         (DIMINDEX_CONV (lhs (lhand (concl th))))
         (SYM (NUM_REDUCE_CONV w))) in
      MATCH_MP th pth in
    let [pth8; _; _; _; pth4; _; pth2; _] = mk_pth 8 in
    cleanup read_int16 pth2,
    cleanup read_int32 pth4,
    cleanup read_int64 pth8 in

  let pthbn4,pthbi4 =
    let th = prove
     (`dimindex(:N) = 8 * n ==>
       read_word n (APPEND (bytelist_of_num n a) l) =
       SOME ((word a:N word), l)`,
      DISCH_THEN (fun dth ->
        SUBGOAL_THEN `read_word_n n (APPEND (bytelist_of_num n a) l) =
          SOME (a MOD 256 EXP n, l)` (fun th ->
          REWRITE_TAC [read_word; th; obind; CONV_RULE NUM_REDUCE_CONV
            (REWRITE_RULE [dth; EXP_MULT] WORD_MOD_SIZE)]) THEN
        REWRITE_TAC [read_word_n_eq_some] THEN
        EXISTS_TAC `bytelist_of_num n a` THEN
        REWRITE_TAC [LENGTH_BYTELIST_OF_NUM; NUM_OF_BYTELIST_OF_NUM])) in
    let th2 = prove
     (`dimindex(:N) = 8 * n ==>
       read_word n (APPEND (bytelist_of_int n a) l) =
       SOME ((iword a:N word), l)`,
      DISCH_THEN (fun dth -> REWRITE_TAC [bytelist_of_int; MP th dth; iword;
        INT_OF_NUM_POW; dth; EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV)) in
    W f_f_ (REWRITE_RULE [SYM read_int32] o
      C MATCH_MP (TRANS DIMINDEX_32 (ARITH_RULE `32 = 8 * 4`))) (th,th2) in

  let nsa0 = Array.init 256 (fun i ->
    NUM_SHIFT_ADD_CONV (mk_comb (mk_comb (mk_comb (`num_shift_add`,
      mk_numeral (num i)), `0`), `8`)))
  and nsaS = Array.init 256 (fun i ->
    NUM_SHIFT_ADD_CONV (mk_comb (mk_comb (mk_comb (`num_shift_add`,
      mk_numeral (num i)), `NUMERAL r`), `8`))) in
  let num_shift_add_conv a' r' = match rand r' with
  | Const("_0",_) -> nsa0.(Num.int_of_num (dest_numeral a'))
  | r' -> INST [r',er] nsaS.(Num.int_of_num (dest_numeral a')) in
  let rec prove_hyps n = function
  | Comb(Comb(Const("CONS",_),Comb(Const("word",_),a')),l') ->
    if n = 1 then [a',ai.(0); l',el],I else
    let n' = n - 1 in
    let ls,f = prove_hyps n' l' in
    let r' = fst (hd ls) in
    let th = num_shift_add_conv a' r' in
    let r2' = rhs (concl th) in
    (r2',ri.(n')) :: (a',ai.(n')) :: ls, PROVE_HYP th o f
  | _ -> failwith "READ_WORD_CONV" in

  function
  | Comb(Const("read_byte",_),l') ->
    let ls,f = prove_hyps 1 l' in f (INST ls pthi1)
  | Comb(Const("read_int16",_),l') ->
    let ls,f = prove_hyps 2 l' in f (INST ls pthi2)
  | Comb(Const("read_int32",_),l') ->
    (try let ls,f = prove_hyps 4 l' in f (INST ls pthi4)
    with Failure _ as e ->
      match l' with
      | Comb(Comb(Const("APPEND",_),
          Comb(Comb(Const("bytelist_of_num",_),_),a)),l') ->
        INST [a,ea; l',el] pthbn4
      | Comb(Comb(Const("APPEND",_),
          Comb(Comb(Const("bytelist_of_int",_),_),a)),l') ->
        INST [a,eai; l',el] pthbi4
      | _ -> raise e)
  | Comb(Const("read_int64",_),l') ->
    let ls,f = prove_hyps 8 l' in f (INST ls pthi8)
  | _ -> failwith "READ_WORD_CONV";;

(* ------------------------------------------------------------------------- *)
(* Extension of the simd function family to 3 operands.                      *)
(* ------------------------------------------------------------------------- *)

let msimd2 = new_definition
 `(msimd2:(M word->N word->N word->N word)->
        ((M)tybit0)word->((N)tybit0)word->((N)tybit0) word->((N)tybit0) word) f m x y =
    word_join (f (word_subword m (dimindex(:M),dimindex(:M)))
                 (word_subword x (dimindex(:N),dimindex(:N)))
                 (word_subword y (dimindex(:N),dimindex(:N))))
              (f (word_subword m (0,dimindex(:M)))
                 (word_subword x (0,dimindex(:N)))
                 (word_subword y (0,dimindex(:N))))`;;

let msimd4 = new_definition
 `msimd4 (f:M word->N word->N word->N word) = msimd2 (msimd2 f)`;;

let msimd8 = new_definition
 `msimd8 (f:M word->N word->N word->N word) = msimd2 (msimd4 f)`;;

let msimd16 = new_definition
 `msimd16 (f:M word->N word->N word->N word) = msimd2 (msimd8 f)`;;

let simd32 = new_definition
 `simd32 (f: N word -> N word -> N word) = simd2 (simd16 f)`;;
