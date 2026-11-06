(* ========================================================================= *)
(*           Parsing and printing for bitmatch expressions.                  *)
(*                                                                           *)
(* This supports term constructions like                                     *)
(*                                                                           *)
(*   bitmatch (word 17) with                                                 *)
(*   | [hi3:3; 0b00:2; lo3:3] -> foo hi3 lo3                                 *)
(*   | [hi3:3; 0b1:1; lo4:4]  -> bar hi3 lo4                                 *)
(*   | [0b1010101:7; b]       -> baz b                                       *)
(*                                                                           *)
(* which decomposes the number 17 = 0b00010001 into the 3 high bits          *)
(* (hi3 = 0), a 1 bit in the middle, and the 4 low bits (lo4 = 1) and calls  *)
(* `bar`.  The patterns are written with the low bits on the right.          *)
(* A pattern variable without a digit matches one bit as a bool.             *)
(*                                                                           *)
(*                (c) Copyright, Mario Carneiro 2020                         *)
(* ========================================================================= *)

needs "Library/words.ml";;

prioritize_num();;

(* Like CHOOSE, but the variable is the same as the one in the existential *)

let TRIV_CHOOSE =
  let P = `P:A->bool` and Q = `Q:bool` and an = `(/\)` in
  let pth = (* `(\x:A. Q /\ P x) = P, (?) P |- Q` *)
    let th1 = AP_THM (ASSUME `(\x:A. Q /\ P x) = P`) `x:A` in
    let th1 = TRANS (SYM th1) (BETA `(\x:A. Q /\ P x) x`) in
    let th1 = CONJUNCT1 (EQ_MP th1 (ASSUME `(P:A->bool) x`)) in
    let th1 = GEN `x:A` (DISCH `(P:A->bool) x` th1) in
    let th2 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM EXISTS_DEF P) in
    MP (SPEC `Q:bool` (EQ_MP th2 (ASSUME `(?) (P:A->bool)`))) th1 in
  fun th1 th2 ->
    try let P' = rand (concl th1) in
        let v,bod = dest_abs P' in
        let Q' = concl th2 in
        let anQ = mk_comb (an, Q') in
        let th3 = DEDUCT_ANTISYM_RULE (CONJ th2 (ASSUME bod))
          (CONJUNCT2 (ASSUME (mk_comb (anQ, bod)))) in
        let th4 = AP_TERM anQ (BETA (mk_comb (P', v))) in
        let th5 = PINST [snd(dest_var v),aty] [P',P; Q',Q] pth in
        PROVE_HYP th1 (PROVE_HYP (ABS v (TRANS th4 th3)) th5)
    with Failure _ -> failwith "TRIV_CHOOSE";;

let (WITH_GOAL:(term->tactic)->tactic) = fun tac (_,w as st) -> tac w st;;

let _BITMATCH = new_definition `_BITMATCH (s:N word) c = _MATCH (val s) c`;;
let _ELSEPATTERN = new_definition `_ELSEPATTERN (e:B) (a:A) = \x. e = x`;;

let bitpat =
  let th = prove
    (`?x:num#(num->bool). !a. SND x a ==> a < 2 EXP FST x`,
    EXISTS_TAC `0, \i:num. F` THEN REWRITE_TAC[SND]) in
  new_type_definition "bitpat" ("mk_bitpat","dest_bitpat") th;;

let pat_size = new_definition `pat_size p = FST (dest_bitpat p)`;;
let pat_set = new_definition `pat_set p = SND (dest_bitpat p)`;;

let pat_set_lt = prove (`!p s. pat_set p s ==> s < 2 EXP pat_size p`,
  REWRITE_TAC [pat_set; pat_size; bitpat]);;

let pat_thm = prove (`p = mk_bitpat (n, f) /\ (!a. f a ==> a < 2 EXP n) ==>
  pat_size p = n /\ !s. pat_set p s = f s`,
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `dest_bitpat (mk_bitpat (n,f)) = (n,f)`
    (fun th -> ASM_REWRITE_TAC [pat_size; pat_set; th]) THEN
  ASM_REWRITE_TAC [GSYM (CONJUNCT2 bitpat)] THEN
  FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP pat_set_lt));;

let NILPAT = new_definition `NILPAT = mk_bitpat(0,\s:num. s = 0)`;;

let NILPAT_pat_size,NILPAT_pat_set = (CONJ_PAIR o prove)
 (`pat_size NILPAT = 0 /\ !s. pat_set NILPAT s <=> s = 0`,
  MATCH_MP_TAC pat_thm THEN REWRITE_TAC [NILPAT] THEN
  STRIP_TAC THEN DISCH_THEN SUBST1_TAC THEN ARITH_TAC);;

let CONSPAT = new_definition `CONSPAT p (a:N word) =
  let n = dimindex(:N) in
  mk_bitpat(n + pat_size p,
    \s:num. (?t. pat_set p t /\ s = val a + 2 EXP n * t))`;;

let CONSPAT_pat_size,CONSPAT_pat_set = (CONJ_PAIR o prove)
 (`pat_size (CONSPAT p (a:N word)) = dimindex(:N) + pat_size p /\
   !s. pat_set (CONSPAT p (a:N word)) s <=>
     ?t. pat_set p t /\ s = val a + 2 EXP dimindex(:N) * t`,
  MATCH_MP_TAC pat_thm THEN
  REWRITE_TAC [CONV_RULE (ONCE_DEPTH_CONV let_CONV) CONSPAT] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP dimindex (:N) * SUC t` THEN
  POP_ASSUM (fun th -> REWRITE_TAC [EXP_ADD; LE_MULT_LCANCEL; LE_SUC_LT;
    MATCH_MP pat_set_lt th]) THEN
  REWRITE_TAC [MULT_SUC; LT_ADD_RCANCEL; VAL_BOUND]);;

reserve_words["BITPAT"; "bitmatch"];;

let word1 = new_definition `word1 p = (word (bitval p)):1 word`;;

let BIT0_WORD1 = prove (`bit 0 (word1 b) = b`,
  REWRITE_TAC [word1; BIT_LSB; bitval; VAL_WORD] THEN DIMINDEX_TAC THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC [] THEN ARITH_TAC);;

let VAL_WORD1 = prove (`val (word1 b) = bitval b`,
  REWRITE_TAC [word1; VAL_WORD_BITVAL]);;

let WORD1_ODD = prove (`word1 (ODD n) = word n`,
  CONV_TAC SYM_CONV THEN REWRITE_TAC [word1; WORD_EQ; DIMINDEX_CLAUSES] THEN
  ASM_CASES_TAC `ODD n` THEN
  ASM_REWRITE_TAC[ODD_MOD; BITVAL_CLAUSES; EXP_1; CONG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[GSYM EVEN_MOD; GSYM ODD_MOD; GSYM NOT_ODD]);;

let preparse_bitpat,preparse_bitmatch =
  let bitmatch_ptm = Varp("_BITMATCH",dpty)
  and NILPAT_ptm = Varp("NILPAT",dpty)
  and CONSPAT_ptm = Varp("CONSPAT",dpty)
  and word_ptm = Varp("word",dpty)
  and word1_ptm = Varp("word1",dpty)
  and arb_ptm = Varp("ARB",dpty)
  and ung_ptm = Varp("_UNGUARDED_PATTERN",dpty)
  and seqp_ptm = Varp("_SEQPATTERN",dpty)
  and else_ptm = Varp("_ELSEPATTERN",dpty) in
  let rec pfrees ptm = match ptm with
  | Varp(v,pty) ->
      if v = "" && pty = dpty then []
      else if can get_const_type v || can num_of_string v
              || exists (fun (w,_) -> v = w) (!the_interface) then []
      else [ptm]
  | Constp(_,_) -> []
  | Combp(p1,p2) -> union (pfrees p1) (pfrees p2)
  | Absp(p1,p2) -> subtract (pfrees p2) (pfrees p1)
  | Typing(p,_) -> pfrees p in
  let pgenvar =
    let gcounter = ref 0 in
    fun () -> let count = !gcounter in
              (gcounter := count + 1;
               Varp("BM%PVAR%"^(string_of_int count),dpty)) in
  let pmk_exists v ptm = Combp(Varp("?",dpty),Absp(v,ptm)) in
  let pmk_bitmatch (((_,e),_),cs) =
    let x = pgenvar() and y = pgenvar() in
    let rec pmk_clauses cs = match pmk_clauses_opt cs with
    | Some t -> t
    | None -> Combp(else_ptm, arb_ptm)
    and pmk_clauses_opt cs = match cs with
    | [] -> None
    | (None,res)::cs -> Some (Combp(else_ptm, res))
    | (Some pat,res)::cs ->
      let tx = Combp(Combp(Varp("pat_set",dpty),pat),x)
      and ty = Combp(Combp(Varp("=",dpty),res),y) in
      let t = itlist pmk_exists (pfrees pat) (Combp(Combp(ung_ptm,tx),ty)) in
      Some(Combp(Combp(seqp_ptm, Absp(x, Absp(y, t))), pmk_clauses cs)) in
    Combp(Combp(bitmatch_ptm,e), pmk_clauses cs) in
  let rec to_bitpat p e = match e with
  | Varp("NIL",_) -> p
  | Combp(Combp(Varp("CONS",_),a),e) ->
    let e2 = match a with
    | Typing(a,i) ->
        let a = match a with
        | Varp(s,_) when can num_of_string s -> Combp(word_ptm,a)
        | _ -> a in
        Typing(a,Ptycon("word",[i]))
    | a -> Combp(word1_ptm,a) in
    to_bitpat (Combp(Combp(CONSPAT_ptm,p),e2)) e
  | _ -> raise Noparse in
  let bitpat = parse_preterm >> to_bitpat NILPAT_ptm in
  let pattern = (a (Ident "_") >> (fun _ -> None))
    ||| (bitpat >> fun x -> Some(x)) in
  let clause = pattern ++ (a (Resword "->") ++ parse_preterm >> snd) in
  let clauses =
    possibly (a (Resword "|")) ++
      listof clause (a (Resword "|")) "pattern-match clause" >> snd in
  (a (Resword "BITPAT") ++ bitpat >> snd),
  (a (Resword "bitmatch") ++ parse_preterm ++ a (Resword "with") ++ clauses
    >> pmk_bitmatch);;

install_parser("bitpat",preparse_bitpat);;
install_parser("bitmatch",preparse_bitmatch);;

let pp_print_bitpat,pp_print_colored_bitpat,
    pp_print_bitmatch,pp_print_colored_bitmatch =
  let switch_color (use_color:bool) =
    (* color printer setting *)
    let pp_term = if use_color then pp_print_colored_term else pp_print_term in
    let pp_type = if use_color then pp_print_colored_type else pp_print_type in
    let pp_resword =
      if use_color then pp_print_colored_resword else pp_print_string in

    let rec dest_pat_rev tm =
      match tm with
      | Comb(Comb(Const("CONSPAT",_),p),a) -> a::dest_pat_rev p
      | Const("NILPAT",_) -> []
      | _ -> failwith "dest_pat" in
    let dest_pat = rev o dest_pat_rev in
    let dest_clause tm =
      match snd(strip_exists(body(body tm))) with
      | Comb(Comb(Const("_UNGUARDED_PATTERN",_),lhs),
          Comb(Comb(Const("=",_),res),_)) ->
        (match lhs with
        | Comb(Comb(Const("pat_set",_),pat),_) -> dest_pat pat, res
        | _ -> failwith "dest_clause")
      | _ -> failwith "dest_clause" in
    let rec dest_clauses tm =
      match tm with
      | Comb(Comb(Const("_SEQPATTERN",_),c),cs) ->
          let c = dest_clause c and l,r = dest_clauses cs in c::l,r
      | Comb(Const("_ELSEPATTERN",_),res) -> [],res
      | _ -> failwith "dest_clauses" in
    let f fmt =
      let unword i = function
      | Comb(Const("word",_),a) when is_numeral a ->
        if dest_numeral a </ power_num (num 2) (dest_finty i)
        then a
        else failwith "numeral out of range"
      | a -> a in
      let print_pat = function
      | Comb(Const("word1",_),a) -> pp_term fmt a
      | a -> match type_of a with
        | Tyapp("word",[i]) ->
            (pp_term fmt (unword i a);
            pp_print_string fmt ":";
            pp_type fmt i)
        | _ -> failwith "print_pat" in
      let print_opat = function
      | None -> pp_print_string fmt "_"
      | Some [] -> pp_print_string fmt "[]"
      | Some (x::xs) ->
        (pp_print_string fmt "[";
          print_pat x;
          List.iter (fun x ->
            pp_print_string fmt "; ";
            print_pat x) xs;
          pp_print_string fmt "]") in
      let print_clause p r =
        (print_opat p;
        pp_print_string fmt " -> ";
        pp_term fmt r) in
      let rec print_clauses cls r = match cls,r with
      | [p,res],Const("ARB",_) -> print_clause (Some p) res
      | (p,res)::cs,_ -> (
        print_clause (Some p) res;
        pp_print_break fmt 1 0;
        pp_print_string fmt "| ";
        print_clauses cs r)
      | [],r -> print_clause None r in
      let pp_print_bitpat tm =
        let pat = dest_pat tm in
        (pp_open_hvbox fmt 0;
        pp_print_string fmt "(BITPAT";
        pp_print_space fmt ();
        print_opat (Some pat);
        pp_print_string fmt ")";
        pp_close_box fmt ()) in
      let pp_print_bitmatch = function
      | Comb(Comb(Const("_BITMATCH",_),e),c) ->
          let cls,r = dest_clauses c in
          (pp_open_hvbox fmt 0;
          pp_print_string fmt "(";
          pp_resword fmt "bitmatch ";
          pp_term fmt e;
          pp_resword fmt " with";
          pp_print_break fmt 1 2;
          print_clauses cls r;
          pp_close_box fmt ();
          pp_print_string fmt ")")
      | _ -> failwith "print_bitmatch" in
      pp_print_bitpat,pp_print_bitmatch in
    fst o f, snd o f
  in
  let ppbitpat,ppbitmatch = switch_color false
  and ppbitpatcol,ppbitmatchcol = switch_color true in
  ppbitpat,ppbitpatcol,ppbitmatch,ppbitmatchcol;;

let print_bitpat = pp_print_bitpat std_formatter
and string_of_bitpat = print_to_string pp_print_bitpat;;

let print_bitmatch = pp_print_bitmatch std_formatter
and string_of_bitmatch = print_to_string pp_print_bitmatch;;

install_user_printer("bitpat",pp_print_bitpat);;
install_user_printer("bitmatch",pp_print_bitmatch);;
install_user_color_printer("bitpat",pp_print_colored_bitpat);;
install_user_color_printer("bitmatch",pp_print_colored_bitmatch);;

(* ------------------------------------------------------------------------- *)
(* Some tactics for dealing with bitmatch                                    *)
(* ------------------------------------------------------------------------- *)

let dest_word_ty = function
| Tyapp("word",[i]) -> i
| _ -> failwith "dest_word_ty";;

let SPLIT_IF =
  let th = (UNDISCH_ALL o TAUT)
    `(p ==> a:A = t1) ==> (~p ==> a = t2) ==> a = if p then t1 else t2` in
  let [Var(_,A) as a; p; t1; t2] = frees (concl th) and tnot = `~` in
  fun p' th1 th2 ->
    let a',t1' = dest_eq (concl th1) and
    t2' = snd (dest_eq (concl th2)) in
    (PROVE_HYP (DISCH p' th1) o PROVE_HYP (DISCH (mk_comb(tnot, p')) th2))
    (PINST [type_of a',A] [p',p; a',a; t1',t1; t2',t2] th);;

let MATCH_SEQPATTERN = prove
 (`_MATCH (e:A) (_SEQPATTERN c cs) =
   if ?y:B. c e y then _MATCH e c else _MATCH e cs`,
  COND_CASES_TAC THEN ASM_REWRITE_TAC [_MATCH; _SEQPATTERN]);;

let BITMATCH_SEQPATTERN = prove
 (`_BITMATCH (e:N word) (_SEQPATTERN c cs) =
   if ?y:B. c (val e) y then _BITMATCH e c else _BITMATCH e cs`,
  REWRITE_TAC [_BITMATCH; MATCH_SEQPATTERN]);;

let BITMATCH_SEQPATTERN2 = prove
 (`_BITMATCH (e:N word) (_SEQPATTERN c cs) =
   if ?y:B. c (val e) y then
     _BITMATCH e (_SEQPATTERN c (_ELSEPATTERN ARB))
   else _BITMATCH e cs`,
  REWRITE_TAC [BITMATCH_SEQPATTERN] THEN COND_CASES_TAC THEN REWRITE_TAC []);;

let MATCH_ELSEPATTERN = prove
 (`_MATCH (e:B) (_ELSEPATTERN (a:A)) = a`,
  REWRITE_TAC [_MATCH; _ELSEPATTERN] THEN METIS_TAC[]);;

let BITMATCH_ELSEPATTERN = prove
 (`_BITMATCH (e:N word) (_ELSEPATTERN (a:A)) = a`,
  REWRITE_TAC [_BITMATCH; MATCH_ELSEPATTERN]);;

let pat_extract = new_definition `pat_extract p i b <=>
  (!n. pat_set p n ==> numbit i n = b)`;;

let PAT_EXTRACT_THM =
  let N,n,m,i,p,b = `:N`,`n:num`,`m:num`,`i:num`,`p:bitpat`,`b:bool`
  and a,lt,pl,nb,di = `a:N word`,`(<)`,`(+)`,`numbit`,`dimindex(:N)` in
  let word1_eq = prove
   (`pat_extract (CONSPAT p (word1 b)) 0 b`,
    REWRITE_TAC [pat_extract; numbit; CONSPAT_pat_set; word1; VAL_WORD] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
    DIMINDEX_TAC THEN NUM_REDUCE_TAC THEN
    REWRITE_TAC [DIV_1; EVEN_ADD; GSYM NOT_EVEN; EVEN_DOUBLE] THEN
    BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC [bitval] THEN ARITH_TAC) in

  let word_lt = (UNDISCH_ALL o prove)
   (`dimindex(:N) = n ==> numbit i m = b ==> (i < n <=> T) ==>
     pat_extract (CONSPAT p (word m:N word)) i b`,
    REWRITE_TAC[] THEN REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN
    REWRITE_TAC [pat_extract; CONSPAT_pat_set; numbit] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
    REWRITE_TAC [VAL_WORD; ODD_MOD; DIV_MOD] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC [MULT_SYM] THEN
    REWRITE_TAC [GSYM (CONJUNCT2 EXP)] THEN
    ONCE_REWRITE_TAC [GSYM MOD_ADD_MOD] THEN
    FIRST_X_ASSUM (SUBST1_TAC o GSYM o
      MATCH_MP (ARITH_RULE `m <= n ==> (m + (n - m) = n:num)`) o
      REWRITE_RULE [GSYM LE_SUC_LT]) THEN
    REWRITE_TAC [EXP_ADD; MOD_MOD] THEN ONCE_REWRITE_TAC [MULT_AC] THEN
    REWRITE_TAC [MOD_MULT; ADD_0; MOD_MOD_REFL]) in

  let word_skip = (UNDISCH_ALL o prove)
   (`dimindex(:N) = n ==> m + n = i ==> pat_extract p m b ==>
     pat_extract (CONSPAT p (a:N word)) i b`,
    REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN
    REWRITE_TAC [pat_extract; CONSPAT_pat_set; numbit] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
    POP_ASSUM (fun th -> POP_ASSUM (fun f ->
      REWRITE_TAC [GSYM (MATCH_MP f th)])) THEN
    REWRITE_TAC [SPECL [m;`dimindex(:N)`] ADD_SYM] THEN
    REWRITE_TAC [EXP_ADD; GSYM DIV_DIV] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    IMP_REWRITE_TAC [DIV_MULT_ADD; DIV_LT; ADD; VAL_BOUND; EXP_2_NE_0]) in

  let rec go = function
  | Comb(Comb(Const("CONSPAT",_),p'),a'),i' ->
    let i'' = dest_numeral i' in
    let aty = type_of a' in
    let Tyapp(_,[N']) = aty in
    let n'' = dest_finty N' in
    if i'' </ n'' then
      match a' with
      | Comb(Const("word1",_),b') -> INST [p',p; b',b] word1_eq
      | Comb(Const("word",_),m') when is_numeral m' ->
        let th = INST_TYPE [N',N] word_lt in
        let th1 = DIMINDEX_CONV (inst [N',N] di) in
        let n' = rhs (concl th1) in
        let th2 = NUMBIT_CONV (mk_comb (mk_comb (nb,i'),m')) in
        let b' = rhs (concl th2) in
        let th3 = NUM_LT_CONV (mk_comb (mk_comb (lt,i'),n')) in
        (PROVE_HYP th3 o PROVE_HYP th2 o PROVE_HYP th1)
          (INST [i',i; m',m; n',n; p',p; b',b] th)
      | _ -> failwith "PAT_EXTRACT_THM: not a constant at this position"
    else
      let th = INST_TYPE [N',N] word_skip in
      let th1 = DIMINDEX_CONV (inst [N',N] di) in
      let n' = rhs (concl th1) in
      let m' = mk_numeral (sub_num i'' n'') in
      let th2 = NUM_ADD_CONV (mk_comb (mk_comb (pl,m'),n')) in
      let th3 = go (p', m') in
      let b' = rand (concl th3) in
      (PROVE_HYP th3 o PROVE_HYP th2 o PROVE_HYP th1)
        (INST [i',i; m',m; n',n; p',p; b',b; a',mk_var("a",aty)] th)
  | _ -> failwith "PAT_EXTRACT_THM: out of range"
  in go;;

(* (pat_to_bit false `i` `pat_set p (val e)`) proves
    `bit i e |- ~pat_set p (val e)` or
    `~bit i e |- ~pat_set p (val e)`
    (pat_to_bit true `i` `pat_set p (val e)`) proves
    `pat_set p (val e) |- ~bit i e` or
    `pat_set p (val e) |- bit i e` *)
let pat_to_bit =
  (* thT := ~bit i e, pat_extract p i T |- ~pat_set p (val e)
      thF := bit i e, pat_extract p i F |- ~pat_set p (val e) *)
  let thT_pos,thF_pos =
    (* TODO: I got frustrated with tactics so this is just a direct proof. *)
    let a = PURE_REWRITE_RULE [pat_extract] (ASSUME `pat_extract p i b`) in
    let a = UNDISCH (SPEC `val (e:N word)` a) in
    let th = TRANS (SYM NUMBIT_VAL) a in
    EQT_ELIM (INST [`T`,`b:bool`] th), EQF_ELIM (INST [`F`,`b:bool`] th) in
  let thT_neg,thF_neg =
    let f x y = NOT_INTRO (DISCH `pat_set p (val (e:N word))`
      (MP (NOT_ELIM x) y)) in
    f (ASSUME `~bit i (e:N word)`) thT_pos,
    f thF_pos (ASSUME `bit i (e:N word)`) in
  let N,i,e,p = `:N`,`i:num`,`e:N word`,`p:bitpat` in
  fun pos i' -> function
  | Comb(Comb(Const("pat_set",_),p'),
      Comb(Const("val",Tyapp(_,[Tyapp(_, [N']); _])),e')) ->
    let thp = PAT_EXTRACT_THM (p', i') in
    let th = match rand (concl thp) with
    | Const("T",_) -> if pos then thT_pos else thT_neg
    | Const("F",_) -> if pos then thF_pos else thF_neg
    | _ -> failwith "pat_to_bit" in
    PROVE_HYP thp (PINST [N',N] [i',i; e',e; p',p] th)
  | _ -> failwith "pat_to_bit";;

let bm_analyze_pat sz =
  let A = Array.make sz None in
  let rec go i = function
  | Comb(Comb(Const("CONSPAT",_),p),a) ->
    let n = Num.int_of_num (dest_finty (dest_word_ty (type_of a))) in
    if i + n > sz then
      raise (Invalid_argument "incorrect bit length") else
    let () = match a with
    | Comb(Const("word1",_),a) ->
      A.(i) <- (match a with
        | Const("T",_) -> Some true
        | Const("F",_) -> Some false
        | Var(_,_) -> None
        | _ -> failwith "bm_analyze_pat")
    | Comb(Const("word",_),Comb(Const("NUMERAL",_),a)) ->
      let rec analyze_num n a = match a with
      | Comb(Const("BIT0",_),a) ->
        (A.(n) <- Some false; analyze_num (n+1) a)
      | Comb(Const("BIT1",_),a) ->
        (A.(n) <- Some true; analyze_num (n+1) a)
      | Const("_0",_) -> Array.fill A n (sz - n) (Some false)
      | _ -> failwith "bm_analyze_pat" in
      analyze_num i a
    | Var(_,_) -> Array.fill A i n None
    | _ -> failwith "bm_analyze_pat" in
    go (i + n) p
  | Const("NILPAT",_) ->
    if i = sz then () else
    raise (Invalid_argument "incorrect bit length")
  | Abs(_,c) -> go i c
  | Comb(Const("?",_),c) -> go i c
  | Comb(Comb(Const("_UNGUARDED_PATTERN",_),c),_) -> go i c
  | Comb(Comb(Const("pat_set",_),c),_) -> go i c
  | _ -> failwith "bm_analyze_pat" in
  fun pat ->
    try go 0 pat; A
    with Invalid_argument _ -> failwith (sprintf
      "bm_analyze_pat: pattern %s has incorrect bit length"
      (string_of_term pat));;

let rec bm_analyze_clauses sz = function
| Comb(Comb(Const("_SEQPATTERN",_),c),cs) ->
  let pat = (lhand o lhand o snd o strip_exists o body o body) c in
  bm_analyze_pat sz pat :: bm_analyze_clauses sz cs
| _ -> [];;

(* (bm_skip_clause f `_BITMATCH e (_SEQPATTERN r rs)`) returns
   `A |- _BITMATCH e (_SEQPATTERN r rs) = _BITMATCH e rs` if
   (f `pat_set p (val e)`) proves `A |- ~pat_set p (val e)`
   (probably via pat_to_bit false) *)
let bm_skip_clause =
  let th = (UNDISCH o prove)
    (`(?) (r (val e)) = F ==>
      (_BITMATCH e (_SEQPATTERN r rs):B) = _BITMATCH (e:N word) rs`,
    REPEAT DISCH_TAC THEN REWRITE_TAC [BITMATCH_SEQPATTERN] THEN
    CONV_TAC (ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC []) in
  let N,B,e,r,rs =
    `:N`,`:B`,`e:N word`,`r:num->B->bool`,`rs:num->B->bool` in

  (* (strip_ex `x` `A |- P[x] = F`) proves `A |- (?x. P[x]) = F` *)
  let strip_ex =
    let th1 = (UNDISCH o prove)
      (`(P = \x:A. F) ==> (?) P = F`, DISCH_TAC THEN ASM_REWRITE_TAC[]) in
    let A = `:A` and P = `P:A->bool` in
    fun x th ->
      let th' = ABS x th in
      PROVE_HYP th' (PINST [type_of x,A] [lhs (concl th'),P] th1) in

  (* (skip_guard `A` `B`) proves `~A |- _UNGUARDED_PATTERN A B = F` *)
  let skip_guard =
    let th = (UNDISCH o prove)
      (`~A ==> _UNGUARDED_PATTERN A B = F`,
      DISCH_TAC THEN ASM_REWRITE_TAC [_UNGUARDED_PATTERN]) in
    let A = `A:bool` and B = `B:bool` in
    fun A' B' -> INST [A',A; B',B] th in

  fun f -> function
  | Comb(Comb(Const("_BITMATCH",ty),e'),
      Comb(Comb(Const("_SEQPATTERN",_),c),rs')) ->
    let Tyapp(_, [N']),Tyapp(_, [_; B']) = dest_fun_ty ty in
    let th = PINST [N',N;B',B] [e',e; c,r; rs',rs] th in
    let ex,h = dest_comb (lhs (hd (hyp th))) in
    let th2 = BETA_CONV h in
    let th3 = AP_TERM ex th2 in
    let rec skip_exs = function
    | Comb(Const("?",_),Abs(y,c)) -> strip_ex y (skip_exs c)
    | Comb(Comb(Const("_UNGUARDED_PATTERN",_),p),res) ->
      PROVE_HYP (f p) (skip_guard p res)
    | _ -> failwith "skip_exs" in
    PROVE_HYP (TRANS th3 (skip_exs (rhs (concl th3)))) th
  | _ -> failwith "bm_skip_clause";;

type 'a discrim_tree =
    Leaf_dt of 'a
  | Split_dt of int * term * 'a discrim_tree * 'a discrim_tree;;

let rec map_dt f = function
| Leaf_dt a -> Leaf_dt (f a)
| Split_dt(i, bit, tr1, tr2) ->
  Split_dt(i, bit, map_dt f tr1, map_dt f tr2);;

let bm_build_tree' =
  let bit_tm =
    let N = `:N` in
    fun i e ->
      let Tyapp("word",[N']) = type_of e in
      let bit = mk_const("bit",[N',N]) in
      mk_comb(mk_comb(bit,i),e) in

  (* (seqp_rand `r` `A |- _BITMATCH e rs1 = _BITMATCH e rs2`) proves
     `A |- _BITMATCH e (_SEQPATTERN r rs1) =
           _BITMATCH e (_SEQPATTERN r rs2)` *)
  let seqp_rand =
    let th = (UNDISCH o prove)
      (`_BITMATCH (e:N word) (rs1:num->B->bool) = _BITMATCH e rs2 ==>
        _BITMATCH e (_SEQPATTERN r rs1) = _BITMATCH e (_SEQPATTERN r rs2)`,
      DISCH_TAC THEN ASM_REWRITE_TAC [BITMATCH_SEQPATTERN]) in
    let [rs1; e; r; rs2] = frees (concl th) and N,B = `:N`,`:B` in
    fun r' th' ->
      match dest_eq (concl th') with
      | Comb(Comb(Const(_,ty),e'),rs1'),Comb(_,rs2') ->
      let Tyapp(_, [N']),Tyapp(_, [_; B']) = dest_fun_ty ty in
      PROVE_HYP th' (PINST [N',N; B',B] [e',e; r',r; rs1',rs1; rs2',rs2] th)
      | _ -> failwith "seqp_rand" in

  let aMerge a b = match a,b with
  | None,_ -> a
  | _,None -> None
  | Some(a0,a1),Some false -> Some(a0+1, a1)
  | Some(a0,a1),Some true -> Some(a0, a1+1) in

  fun sz cls -> function
  | Comb(Comb(Const("_BITMATCH",_),e) as m, cs) as tm ->
    let rec build eqth cls cs =
      let analysis = Array.make sz (Some(0,0)) in
      let _ = List.iter (Array.iteri
        (fun i a -> analysis.(i) <- aMerge analysis.(i) a)) cls in
      let r =
        let r = ref None in
        let f i a = match a with
        | Some(n1,n2) when n1 != 0 && n2 != 0 ->
          let v = abs (n1 - n2) in
          (match !r with
          | Some(v',_) when v' <= v -> ()
          | _ -> r := Some(v, i))
        | _ -> () in
        (Array.iteri f analysis; !r) in
      match r with
      | None -> Leaf_dt eqth
      | Some(_,i) ->
        let ii = mk_numeral (num i) in
        let bit = bit_tm ii e in
        let skip_th sc th =
          let sm, rs' = dest_comb (lhs (concl th)) in
          let tm = mk_comb (sm, mk_comb (sc, rs')) in
          TRANS (bm_skip_clause (pat_to_bit false ii) tm) th in
        let rec split_ths = function
        | [], cs -> let th = REFL (mk_comb(m,cs)) in [],[],th,th
        | cl::cls, Comb(Comb(Const("_SEQPATTERN",_),c) as sc,cs) ->
          let cls1,cls2,th1,th2 = split_ths(cls, cs) in
          if let Some(b) = cl.(i) in b then
            cls1, cl::cls2, skip_th sc th1, seqp_rand c th2
          else
            cl::cls1, cls2, seqp_rand c th1, skip_th sc th2
        | cl::cls, cs ->
          let cls1,cls2,th1,th2 = split_ths(cls, cs) in
          if let Some(b) = cl.(i) in b then
            cls1, cl::cls2, th1, th2
          else
            cl::cls1, cls2, th1, th2
        | _ -> failwith "split_ths" in
        let cls1,cls2,th1,th2 = split_ths(cls, cs) in
        let tr1 = build (TRANS eqth th1) cls1 (rand (rhs (concl th1)))
        and tr2 = build (TRANS eqth th2) cls2 (rand (rhs (concl th2))) in
        Split_dt(i, bit, tr1, tr2) in
    build (REFL tm) cls cs
  | _ -> failwith "bm_build_tree'";;

let bm_build_tree = function
| Comb(Comb(Const("_BITMATCH",_),e),cs) as tm ->
  let sz = Num.int_of_num (dest_finty (dest_word_ty (type_of e))) in
  let cls = bm_analyze_clauses sz cs in
  cls, bm_build_tree' sz cls tm
| _ -> failwith "bm_build_tree";;

let BM_IF_CONV =
  let rec of_tree = function
  | Leaf_dt th -> th
  | Split_dt(_, bit, tr1, tr2) -> SPLIT_IF bit (of_tree tr2) (of_tree tr1) in
  of_tree o snd o bm_build_tree;;

let MATCH_EQ = prove
 (`(r:A->B->bool) e = (\y. x = y) ==> _MATCH e r = x`,
  REWRITE_TAC [_MATCH] THEN DISCH_THEN SUBST1_TAC THEN METIS_TAC[]);;

let bitpat_inverts = new_definition
 `bitpat_inverts p f (x:A) <=> (!y. pat_set p y ==> f y = x)`;;

let bitpat_down = new_definition
 `bitpat_down(:N) (f:num->A) (n:num) = f (n DIV 2 EXP dimindex(:N))`;;

let CONSPAT_down_inverts = prove
 (`bitpat_inverts p f (x:A) ==>
   bitpat_inverts (CONSPAT p (a:N word)) (bitpat_down(:N) f) x`,
  REWRITE_TAC [bitpat_inverts; bitpat_down; CONSPAT_pat_set] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  IMP_REWRITE_TAC [DIV_MULT_ADD; DIV_LT; VAL_BOUND; EXP_2_NE_0] THEN
  ASM_REWRITE_TAC [ADD]);;

let CONSPAT_word_inverts = prove
 (`bitpat_inverts (CONSPAT p (a:N word)) word a`,
  REWRITE_TAC [bitpat_inverts; CONSPAT_pat_set] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
  REWRITE_TAC [WORD_VAL_GALOIS; MOD_MULT_ADD] THEN
  REWRITE_TAC [GSYM WORD_VAL_GALOIS; WORD_VAL]);;

let bitpat_inverts_comp = MESON [bitpat_inverts; o_DEF]
 `bitpat_inverts p f (x:A) ==> bitpat_inverts p (g o f) (g x:B)`;;

let CONSPAT_word1_inverts =
  (* `bitpat_inverts (CONSPAT p (word1 b)) (bit 0 o word) b` *)
  REWRITE_RULE [BIT0_WORD1]
    (PART_MATCH rand (MATCH_MP bitpat_inverts_comp CONSPAT_word_inverts)
      (lhs (concl BIT0_WORD1)));;

(* Given a pattern `p` and a target variable `z`,
  (build_inverts `p`) produces an association list mapping `z`
  to `|- bitpat_inverts p f z` for some term `f` not containing `z`. *)
let build_inverts =
  let N,A,p,a,f,x,b =
    `:N`,`:A`,`p:bitpat`,`a:N word`,`f:num->A`,`x:A`,`b:bool`
  and th0 = ASSUME `bitpat_inverts p f (x:A)`
  and th1 = UNDISCH CONSPAT_down_inverts in
  let rec go = function
  | Const("NILPAT",_),_ -> []
  | (Comb(Comb(Const("CONSPAT",_),p'),a') as cp),thunk ->
    let Tyapp(_, [N']) = type_of a' in
    let next th =
      let th' = PINST [N',N] [a',a] th1 in
      let Comb(Comb(_,p'),f') = rator (concl th') in
      PROVE_HYP th' (INST [p',p; f',f] th) in
    let var v thv =
      let th = thunk() in
      let f' = rand (rator (concl thv)) in
      let th' = PROVE_HYP thv (PINST [type_of v,A] [cp,p; f',f; v,x] th) in
      (v,th') :: go (p', fun () -> next th) in
    (match a' with
    | Var(_,_) -> var a' (PINST [N',N] [p',p; a',a] CONSPAT_word_inverts)
    | Comb(Const("word1",_), (Var(_,_) as b')) ->
      var b' (INST [p',p; b',b] CONSPAT_word1_inverts)
    | _ -> go (p', next o thunk))
  | _ -> failwith "build_inverts" in
  fun p' -> go (p', fun () -> th0);;


(* Given `bitmatch e with p -> res | ...` proves
   `bit_set p (val e) |- (bitmatch e with p -> res | ...) = res`,
  and given `bitmatch e with _ -> res` proves
  `(bitmatch e with _ -> res) = res`. *)
let BM_FIRST_CASE_CONV =
  let th1 = (UNDISCH o prove)
   (`r (val (e:N word)) = (\y:A. x = y) ==> _BITMATCH e (_SEQPATTERN r s) = x`,
    DISCH_TAC THEN
    ASM_REWRITE_TAC [BITMATCH_SEQPATTERN; _BITMATCH; MESON[] `?y:A. x=y`] THEN
    POP_ASSUM (ACCEPT_TAC o MATCH_MP MATCH_EQ)) in
  let th2 = (UNDISCH o METIS[_UNGUARDED_PATTERN])
    `A ==> (_UNGUARDED_PATTERN A B <=> B)` in
  let th3 = EQ_MP (SYM th2) (ASSUME `B:bool`) in
  let th4 = (UNDISCH_ALL o prove)
   (`bitpat_inverts p f (x:A) ==> pat_set p e ==> f e = x`,
    DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [bitpat_inverts])) in
  let thg1,thg2 = (CONJ_PAIR o UNDISCH o METIS[_UNGUARDED_PATTERN])
    `_UNGUARDED_PATTERN A B ==> A /\ B` in
  let nty,eA,eB,ep,ef,ex = `:N`,`A:bool`,`B:bool`,`p:bitpat`,`f:num->A`,`x:A`
  and ee,ea,er,es = `e:N word`,`a:A`,`r:num->A->bool`,`s:num->A->bool` in
  function
  | Comb(Comb(Const("_BITMATCH",_),e),
      Comb(Comb(Const("_SEQPATTERN",_), (Abs(x,Abs(y,c')) as c)),cs)) as tm ->
    let A' = type_of tm in
    let N = dest_word_ty (type_of e) in
    let val_e = mk_comb (mk_const("val", [N,nty]), e) in
    let zs, Comb(Comb(Const("_UNGUARDED_PATTERN",_),
      (Comb((Comb(_,p) as mp),_) as ps)),restm) = strip_exists c' in
    let res = lhand restm in
    let instAB = INST [ps,eA; restm,eB] in
    let ps' = mk_comb (mp, val_e) in
    let th' = if zs = [] then instAB th2 else
      let inverts = build_inverts p in
      let rec prove_ex c1 pr eqth = match c1 with
      | Comb(Const("?",_),Abs(z,c')) ->
        let inv = assoc z inverts in
        let f = lhand (concl inv) in
        let inv = PROVE_HYP inv (PINST [type_of z,aty]
          [p,ep; f,ef; z,ex; x,`e:num`] th4) in
        let abr = mk_abs (z, lhs (concl eqth)) in
        let eqth1 = TRANS (AP_TERM abr (ASSUME (concl inv)))
          (BETA (mk_comb (abr, z))) in
        let pr',th = prove_ex c' (PROVE_HYP inv o pr) (TRANS eqth1 eqth) in
        pr', TRANS (SYM eqth1) (TRIV_CHOOSE (ASSUME c1) th)
      | _ -> pr, TRANS (PROVE_HYP (instAB thg1) (pr eqth)) (instAB thg2) in
      let pr,thR = prove_ex c' I (REFL res) in
      DEDUCT_ANTISYM_RULE (itlist SIMPLE_EXISTS zs (instAB th3)) (pr thR) in
    let th' = INST [val_e,x] (TRANS (BETA (mk_comb (c, x))) (ABS y th')) in
    PROVE_HYP th' (PINST [N,nty; A',aty]
      [e,ee; res,ex; c,er; cs,es] th1)
  | Comb(Comb(Const("_BITMATCH",_),e), Comb(Const("_ELSEPATTERN",_), a)) ->
    let A' = type_of a in
    let N = dest_word_ty (type_of e) in
    PINST [N,nty; A',aty] [e,ee; a,ea] BITMATCH_ELSEPATTERN
  | _ -> failwith "BM_FIRST_CASE_CONV";;

let bm_add_pos tr = function
| Comb(Comb(Const("_BITMATCH",_),e),cs) ->
  let N = dest_word_ty (type_of e) in
  let val_e = mk_comb (mk_const("val", [N,`:N`]), e) in
  let rec build_cases stk mth = function
  | Comb(Comb(Const("_SEQPATTERN",_), Abs(x,Abs(y,c'))),cs) ->
    let ps' = mk_comb (rator (lhand (snd (strip_exists c'))), val_e) in
    let th = itlist (fun n ->
      try PROVE_HYP (pat_to_bit true n ps') with Failure _ -> I) stk mth in
    TRANS th (BM_FIRST_CASE_CONV (rhs (concl th))) :: build_cases stk mth cs
  | _ -> [] in
  let rec build stk = function
  | Leaf_dt mth ->
    Leaf_dt (mth, build_cases stk mth (rand (rhs (concl mth))))
  | Split_dt (i, bit, tr1, tr2) ->
    let stk' = lhand bit :: stk in
    Split_dt (i, bit, build stk' tr1, build stk' tr2) in
  build [] tr
| _ -> failwith "bm_build_pos_tree";;

let bm_build_pos_tree tm =
  let A, tr = bm_build_tree tm in A, bm_add_pos tr tm;;

let rec get_dt A = function
| Leaf_dt a -> [], a
| Split_dt(i, bit, tr1, tr2) ->
  match A.(i) with
  | None -> failwith ("get_dt splitting on " ^ string_of_int i)
  | Some b ->
    let stk,r = get_dt A (if b then tr2 else tr1) in
    (b,bit)::stk, r;;

let BM_CASES tm =
  let A, tr = bm_build_pos_tree tm in
  map (fun cl -> hd (snd (snd (get_dt cl tr)))) A;;

(* (bitpat_matches `p` n) returns None if the pattern `p` would match
   `word n`, and Some(i) where i is the smallest differing bit otherwise.
   It throws if n >= 2^pat_size p. *)
let rec bitpat_matches p i = match p with
| Comb(Comb(Const("CONSPAT",_),p),a) ->
  let N = dest_word_ty (type_of a) in
  let n = Num.int_of_num (dest_finty N) in
  let m = power_num (num 2) (num n) in
  let i' = quo_num i m and a' = mod_num i m in
  let r = match a with
  | Comb(Const("word1",_),Const("T",_)) -> if a' =/ num 1 then None else Some 0
  | Comb(Const("word1",_),Const("F",_)) -> if a' =/ num 0 then None else Some 0
  | Comb(Const("word1",_),Var(_,_)) -> None
  | Comb(Const("word",_),n) ->
    let n' = dest_numeral n in
    if a' =/ n' then None else
    let rec f i r = if i land 1 <> 0 then r else f (i lsr 1) (r+1) in
    Some (f ((Num.int_of_num a') lxor (Num.int_of_num n')) 0)
  | Var(_,_) -> None
  | _ -> failwith "bitpat_matches" in
  (match r with
  | Some j -> Some j
  | None ->
    match bitpat_matches p i' with
    | Some j -> Some (j + n)
    | None -> None)
| Const("NILPAT",_) -> if i =/ num 0 then None else
  failwith "bitpat_matches: out of range"
| Abs(_,c) -> bitpat_matches c i
| Comb(Const("?",_),c) -> bitpat_matches c i
| Comb(Comb(Const("_UNGUARDED_PATTERN",_),c),_) -> bitpat_matches c i
| Comb(Comb(Const("pat_set",_),c),_) -> bitpat_matches c i
| _ -> failwith "bitpat_matches";;

(* (inst_bitpat_numeral `pat_set p (val e)` n) will produce an instantiation
   theta for p and e such that e[theta] = word n, and a proof of
    `|- (pat_set p (val e))[theta]`.

   (inst_bitpat_numeral `pat_set p e` n) will produce an instantiation
   theta for p and e such that e[theta] = n, and a proof of
    `|- (pat_set p e)[theta]`. *)
let inst_bitpat_numeral =
  let en,ep,ex,ei,ea = `n:num`,`p:bitpat`,`x:num`,`i:num`,`a:num`
  and eN,T,F = `:N`,`T`,`F` in
  let dim =
    let dN = `dimindex(:N)` in
    fun N -> DIMINDEX_CONV (inst [N,eN] dN) in

  let w0 = prove (`pat_set NILPAT _0`,
    REWRITE_TAC [NILPAT_pat_set; NUMERAL])
  and wS,(w1T,w1F) =
    let pth = prove
     (`pat_set p x ==>
       pat_set (CONSPAT p (word a:N word)) (num_shift_add a x (dimindex(:N)))`,
      REWRITE_TAC [CONSPAT_pat_set; num_shift_add] THEN
      DISCH_THEN (fun th ->
        EXISTS_TAC ex THEN REWRITE_TAC [th; VAL_WORD; MULT_SYM])) in
    (UNDISCH_ALL o prove)
     (`dimindex(:N) = NUMERAL n ==> num_shift_add a x n = i ==> pat_set p x ==>
       pat_set (CONSPAT p (word (NUMERAL a):N word)) i`,
      REWRITE_TAC [NUMERAL] THEN
      REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN ACCEPT_TAC pth),
    (CONJ_PAIR o UNDISCH o prove)
     (`pat_set p x ==>
       pat_set (CONSPAT p (word1 T)) (BIT1 x) /\
       pat_set (CONSPAT p (word1 F)) (BIT0 x)`,
      REWRITE_TAC [word1; bitval] THEN
      DISCH_THEN (fun th -> CONJ_TAC THEN ASSUME_TAC th) THENL [
        POP_ASSUM (MP_TAC o MP (PINST [`:1`,eN] [`1`,ea] pth)) THEN
        SUBGOAL_THEN
          `num_shift_add 1 x (dimindex(:1)) = num_shift_add (BIT1 0) x (SUC 0)`
          (fun th -> REWRITE_TAC [th; num_shift_add_SUC; num_shift_add_0]) THEN
        CONV_TAC (ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
        REWRITE_TAC [BIT1_0; ONE];
        POP_ASSUM (MP_TAC o MP (PINST [`:1`,eN] [`0`,ea] pth)) THEN
        SUBGOAL_THEN
          `num_shift_add 0 x (dimindex(:1)) = num_shift_add (BIT0 0) x (SUC 0)`
          (fun th -> REWRITE_TAC [th; num_shift_add_SUC; num_shift_add_0]) THEN
        CONV_TAC (ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
        REWRITE_TAC [BIT0_0; ONE]]) in
  let w1F0 = REWRITE_RULE [ARITH_ZERO] (INST [`_0`,ex] w1F) in

  let rec go i = function
  | Comb(Comb(Const("CONSPAT",_),p),a) ->
    let N = dest_word_ty (type_of a) in
    let n = Num.int_of_num (dest_finty N) in
    let m = power_num (num 2) (num n) in
    let i' = quo_num i m and a' = mod_num i m in
    let ls, th' = go i' p in
    let p',x = dest_comb (concl th') in let p' = rand p' in
    (match a with
    | Comb(Const("word1",_),a) ->
      let ls, b = match a with
      | Const("T",_) -> ls,true
      | Const("F",_) -> ls,false
      | Var(_,_) -> let b = a' =/ num 1 in ((if b then T else F),a)::ls, b
      | _ -> failwith "inst_bitpat_numeral" in
      ls, PROVE_HYP th' (
        if b then INST [x,ex; p',ep] w1T
        else if i =/ num 0 then INST [p',ep] w1F0
        else INST [x,ex; p',ep] w1F)
    | _ ->
      let thd = dim N in
      let n' = rand (rhs (concl thd)) in
      let ls, a = match a with
      | Comb(Const("word",_),Comb(Const("NUMERAL",_),a)) -> ls, a
      | Var(_,_) ->
        let n = mk_numeral a' in
        (mk_comb (mk_const ("word", [N,eN]), n), a) :: ls, rand n
      | _ -> failwith "inst_bitpat_numeral" in
      let thn = NUM_SHIFT_ADD_CORE a x n' in
      let e = rhs (concl thn) in
      ls, PROVE_HYP th' (PROVE_HYP thn (PROVE_HYP thd
        (INST [n',en; a,ea; x,ex; e,ei; p',ep] (INST_TYPE [N,eN] wS)))))
  | Const("NILPAT",_) -> [], w0
  | _ -> failwith "inst_bitpat_numeral" in

  let pth1 = SYM (SPEC en NUMERAL)
  and pth2 = (UNDISCH_ALL o prove)
   (`pat_size p = NUMERAL n ==> dimindex(:N) = NUMERAL n ==>
     pat_set p x ==> pat_set p (val (word (NUMERAL x):N word))`,
    DISCH_THEN (SUBST1_TAC o SYM) THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [NUMERAL] THEN IMP_REWRITE_TAC [VAL_WORD_EQ] THEN
    POP_ASSUM (ACCEPT_TAC o MATCH_MP pat_set_lt))
  and conv =
    let ps = `pat_size` in
    REWRITE_CONV [CONSPAT_pat_size; NILPAT_pat_size] THENC
    ONCE_DEPTH_CONV DIMINDEX_CONV THENC REDEPTH_CONV NUM_ADD_CONV o
    mk_comb o (fun tm -> (ps, tm)) in

  let check p i = match bitpat_matches p i with
  | None -> go i p
  | _ -> failwith "inst_bitpat_numeral: number does not match pattern" in

  function
  | Comb(Comb(Const("pat_set",_),p), Comb(Const("val",_), e)) ->
    let N' = dest_word_ty (type_of e) in
    let thd = dim N' in
    let pth2 = (PROVE_HYP thd o PROVE_HYP (conv p) o
       INST [p,ep; rand (rhs (concl thd)),en] o INST_TYPE [N',eN]) pth2 in
    fun i ->
      let ls, th = check p i in
      let e' = rand (concl th) in
      let th1 = PROVE_HYP th (INST ((e',ex)::ls) pth2) in
      (match e with
      | Var(_,_) -> (rand (rand (concl th1)),e)::ls, th1
      | _ when aconv e (rand (rand (concl th1))) -> ls, th1
      | _ -> failwith "inst_bitpat_numeral: pattern failed")
  | Comb(Comb(Const("pat_set",_),p), e) ->
    fun i ->
      let ls, th = check p i in
      let f, e' = dest_comb (concl th) in
      let th1 = INST [e',en] pth1 in
      let th2 = EQ_MP (AP_TERM f th1) th in
      (match e with
      | Var(_,_) -> (rhs (concl th1), e)::ls, th2
      | _ when aconv e (rhs (concl th1)) -> ls, th2
      | _ -> failwith "inst_bitpat_numeral: pattern failed")
  | _ -> failwith "inst_bitpat_numeral";;

let BITMATCH_CONV =
  fun tm -> match tm with
  | Comb(Comb(Const("_BITMATCH",_),
      Comb(Const("word",Tyapp(_,[_;Tyapp(_,[N])])),n)),_) when is_numeral n ->
    let A, tr = bm_build_pos_tree tm in
    let n = Num.int_of_num (dest_numeral n)
    and sz = Num.int_of_num (dest_finty N) in
    let a = Array.init sz (fun i -> Some (n land (1 lsl i) != 0)) in
    (match snd (snd (get_dt a tr)) with
    | th::_ ->
      let ps = hd (hyp th) in
      let ls, th' = inst_bitpat_numeral ps (num n) in
      PROVE_HYP th' (INST ls th)
    | _ -> failwith "BITMATCH_CONV")
  | _ -> failwith "BITMATCH_CONV";;

let BITMATCH_SIMP_CONV asl =
  let pos,neg =
    let rec go = function
    | [] -> [],[]
    | th::ths ->
      let pos,neg = go ths in
      match concl th with
      | Comb(Const("~",_),c) when
        (match snd (strip_exists c) with
        | Comb(Comb(Const("pat_set",_),_),_) -> true
        | _ -> false) -> pos,th::neg
      | Comb(Comb(Const("pat_set",_),_),_) -> th::pos,neg
      | _ -> pos,neg in
    go asl in
  let rec conv = function
  | Comb(Comb(Const("_BITMATCH",_),_),Comb(Const("_ELSEPATTERN",_),_)) as tm ->
    PART_MATCH lhs BITMATCH_ELSEPATTERN tm
  | Comb(Comb(Const("_BITMATCH",_),
      Comb(Const("word",_),n)),_) as tm when is_numeral n -> BITMATCH_CONV tm
  | Comb(Comb(Const("_BITMATCH",_),e),
      Comb(Comb(Const("_SEQPATTERN",_),c),cs)) as tm ->
    let pat = mk_comb (rator (lhand (snd (strip_exists (body (body c))))),
        mk_comb (mk_const ("val", [dest_word_ty (type_of e),`:N`]), e)) in
    let vars = frees (lhand pat) in
    let rec check_pos = function
    | th::ths -> (try
        let _,ls,_ = term_unify vars pat (concl th) in
        PROVE_HYP th (INST ls (BM_FIRST_CASE_CONV tm))
      with Failure _ -> check_pos ths)
    | [] ->
      let rec check_neg = function
      | th::ths -> (try
          let pat' = snd (strip_exists (rand (concl th))) in
          let _,ls,_ = term_unify (frees (lhand pat')) pat' pat in
          let ath = INST ls (SPEC_ALL
            (PURE_REWRITE_RULE [NOT_EXISTS_THM] (ASSUME (concl th)))) in
          let th' = PROVE_HYP th (bm_skip_clause (K ath) tm) in
          TRANS th' (TRY_CONV conv (rhs (concl th')))
        with Failure _ -> check_neg ths)
      | [] ->
        let sz = Num.int_of_num (dest_finty (dest_word_ty (type_of e))) in
        let a = bm_analyze_pat sz pat in
        let rec check_disj = function
        | th::ths -> (try
            let h = concl th in
            let a' = bm_analyze_pat sz h in
            let r = ref None in
            Array.iteri (fun i x -> match x,a'.(i),!r with
              | Some b, Some c, None when b != c -> r := Some i
              | _ -> ()) a;
            let i = match !r with
            | Some i -> mk_numeral (num i)
            | _ -> fail () in
            let th' = PROVE_HYP th (PROVE_HYP (pat_to_bit true i h)
              (bm_skip_clause (pat_to_bit false i) tm)) in
            TRANS th' (TRY_CONV conv (rhs (concl th')))
          with Failure _ -> check_disj ths)
        | [] -> failwith "BITMATCH_SIMP_CONV" in
        check_disj pos in
      check_neg neg in
    check_pos pos
  | _ -> failwith "BITMATCH_SIMP_CONV" in
  conv;;

let rec bitpat_irrefutable = function
| Comb(Comb(Const("CONSPAT",_),p),a) ->
  (match a with
  | Comb(Const("word1",_),Var(_,_)) -> bitpat_irrefutable p
  | Var(_,_) -> bitpat_irrefutable p
  | _ -> false)
| Const("NILPAT",_) -> true
| Abs(_,c) -> bitpat_irrefutable c
| Comb(Const("?",_),c) -> bitpat_irrefutable c
| Comb(Comb(Const("_UNGUARDED_PATTERN",_),c),_) -> bitpat_irrefutable c
| Comb(Comb(Const("pat_set",_),c),_) -> bitpat_irrefutable c
| _ -> failwith "bitpat_irrefutable";;

let bitpat_irrefutable_thm =
  let eN,ee,ee',en,em,ek = `:N`,`e:num`,`e:N word`,`n:num`,`m:num`,`k:num`
  and ep,dN,pl,_1 = `p:bitpat`,`dimindex(:N)`,`(+)`,`1`
  and e2n = `e DIV 2 EXP n`
  and pth,pth1 =
    let pth = prove
     (`dimindex(:N) = n ==> pat_set p (e DIV 2 EXP n) ==>
       pat_set (CONSPAT p (word e:N word)) e`,
      REWRITE_TAC [CONSPAT_pat_set] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      DISCH_THEN (fun th -> EXISTS_TAC `e DIV 2 EXP dimindex(:N)` THEN
        REWRITE_TAC [th; VAL_WORD; ADD_SYM; MULT_SYM;
          GSYM (MATCH_MP DIVISION (SPEC `n:num` EXP_2_NE_0))])) in
    UNDISCH_ALL pth,
    (UNDISCH o prove)
     (`pat_set p (e DIV 2 EXP 1) ==> pat_set (CONSPAT p (word1 (ODD e))) e`,
      REWRITE_TAC [WORD1_ODD] THEN
      ACCEPT_TAC (MATCH_MP pth (DIMINDEX_CONV `dimindex(:1)`)))
  and pth0 = (UNDISCH o prove) (`e < 2 EXP 0 ==> pat_set NILPAT e`,
    REWRITE_TAC [EXP; ARITH_RULE `n < 1 <=> n = 0`; NILPAT_pat_set])
  and pthS = (UNDISCH_ALL o prove) (`n + m = k ==>
    e < 2 EXP k ==> e DIV 2 EXP n < 2 EXP m`,
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    IMP_REWRITE_TAC [EXP_ADD; RDIV_LT_EQ; EXP_2_NE_0])
  and pthW = (UNDISCH_ALL o prove)
   (`dimindex(:N) = n ==> val (e:N word) < 2 EXP n`,
    DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [VAL_BOUND]) in

  let rec build = function
  | Const("NILPAT",_),e -> [], INST [e,ee] pth0
  | Comb(Comb(Const("CONSPAT",_),p),v),e ->
    let pthS n m =
      let th = NUM_ADD_CONV (mk_comb (mk_comb (pl, n), m)) in
      PROVE_HYP th (INST [n,en; m,em; rhs (concl th),ek; e,ee] pthS) in
    (match v with
    | Comb(Const("word1",_),(Var(_,_) as v)) ->
      let ls, th = build (p, vsubst [e,ee; _1,en] e2n) in
      let th' = PROVE_HYP th (INST [lhand (concl th),ep; e,ee] pth1) in
      (rand (rand (lhand (concl th'))),v)::ls,
      PROVE_HYP (pthS _1 (rand (rand (hd (hyp th))))) th'
    | Var(_,ty) ->
      let N = dest_word_ty ty in
      let th1 = DIMINDEX_CONV (inst [N,eN] dN) in
      let n = rhs (concl th1) in
      let ls, th = build (p, vsubst [e,ee; n,en] e2n) in
      let th' = PROVE_HYP th1
        (INST [n,en; lhand (concl th),ep; e,ee] (INST_TYPE [N,eN] pth)) in
      let th' = PROVE_HYP th th' in
      (rand (lhand (concl th')),v)::ls,
      PROVE_HYP (pthS n (rand (rand (hd (hyp th))))) th'
    | _ -> failwith "bitpat_irrefutable_thm: not irrefutable")
  | _ -> failwith "bitpat_irrefutable_thm" in

  fun tm -> match snd (strip_exists tm) with
  | Comb(Comb(Const("pat_set",_),p),(Comb(Const("val",_),e') as e)) ->
    let ls,th = build (p, e) in
    let rec build_ex = function
    | Comb(Const("?",_),Abs(v,c)) as tm ->
      let e = rev_assoc v ls in
      EXISTS (tm, e) (build_ex (vsubst [e,v] c))
    | tm when aconv (concl th) tm -> th
    | _ -> failwith "bitpat_irrefutable_thm: nonlinear pattern" in
    let th = build_ex tm in
    let N = dest_word_ty (type_of e') in
    let th1 = DIMINDEX_CONV (inst [N,eN] dN) in
    let n = rhs (concl th1) in
    if aconv n (rand (rand (hd (hyp th)))) then
      PROVE_HYP (PROVE_HYP th1 (PINST [N,eN] [n,en; e',ee'] pthW)) th
    else failwith "bitpat_irrefutable_thm: incorrect bit length"
  | _ -> failwith "bitpat_irrefutable_thm";;

let ONLY_BITMATCH_CASES_THEN thltac = WITH_GOAL (fun w ->
  let e,cs =
    let f = function
    | Comb(Comb(Const("_BITMATCH",_),_),_) -> true
    | _ -> false in
    (rand F_F I) (dest_comb (find_term f w)) in
  let rec tac thl = function
  | Comb(Comb(Const("_SEQPATTERN",_),Abs(_,Abs(_,c))),cs) ->
    let rec go = function
    | Comb((Const("?",_) as f),Abs(z,c)) ->
      let tm, tac1 = go c in
      mk_comb (f, mk_abs (z, tm)), POP_ASSUM CHOOSE_TAC THEN tac1
    | tm ->
      mk_comb (rator (lhand tm),
        mk_comb (mk_const ("val", [dest_word_ty (type_of e),`:N`]), e)),
      ALL_TAC in
    let tm, tac1 = go c in
    if bitpat_irrefutable c then
      ASSUME_TAC (bitpat_irrefutable_thm tm) THEN
      tac1 THEN POP_ASSUM (fun th -> thltac (th::thl))
    else
      ASM_CASES_TAC tm THENL [
        tac1 THEN POP_ASSUM (fun th -> thltac (th::thl));
        POP_ASSUM (fun th -> tac (th::thl) cs)]
  | _ -> thltac thl in
  tac [] cs);;

let BITMATCH_ASM_CASES_TAC =
  ONLY_BITMATCH_CASES_THEN (fun thl ->
    CONV_TAC (TOP_SWEEP_CONV (BITMATCH_SIMP_CONV thl)) THEN
    MAP_EVERY ASSUME_TAC thl);;

let BITMATCH_CASES_TAC =
  ONLY_BITMATCH_CASES_THEN (CONV_TAC o
    TOP_SWEEP_CONV o BITMATCH_SIMP_CONV);;

(* (bm_seq_numeral `bitmatch e with ...` n) will
   return `word n` and `(bitmatch word n with ...) = res` where `res` is the
   appropriate match branch. Unlike BITMATCH_CONV this also works with matches
   with non-disjoint cases. *)
let bm_seq_numeral = function
| Comb((Comb(Const("_BITMATCH",_),e) as me),cs) ->
  let N = dest_word_ty (type_of e) in
  let sz = Num.int_of_num (dest_finty N) in
  let word = mk_const ("word", [N,`:N`]) in
  let rec mk_fun cs =
    let tm = mk_comb (me, cs) in
    let th = BM_FIRST_CASE_CONV tm in
    let inst e' th = if is_var e then INST [e',e] th else th in
    match cs with
    | Comb(Comb(Const("_SEQPATTERN",_),c),cs') ->
      let ps = hd (hyp th) in
      let pats = Array.init sz (fun i -> try
        Some (bm_skip_clause (pat_to_bit false (mk_numeral (num i))) tm)
      with Failure _ -> None) in
      let f = mk_fun cs' in
      fun n e' ->
        (match bitpat_matches c n with
        | None ->
          let ls, th' = inst_bitpat_numeral ps n in
          PROVE_HYP th' (INST ls th)
        | Some i ->
          let Some th' = pats.(i) in
          let th1 = inst e' th' in
          let th2 = match hd (hyp th1) with
          | Comb(Const("~",_),p) -> EQF_ELIM (WORD_RED_CONV p)
          | p -> EQT_ELIM (WORD_RED_CONV p) in
          TRANS (PROVE_HYP th2 th1) (f n e'))
    | Comb(Const("_ELSEPATTERN",_),_) -> fun _ e' -> inst e' th
    | _ -> failwith "bm_seq_numeral" in
  let f = mk_fun cs in
  fun n -> let e = mk_comb (word, mk_numeral n) in e, f n e
| _ -> failwith "bm_seq_numeral";;

let BITMATCH_SEQ_CONV = function
| Comb(Comb(Const("_BITMATCH",_), Comb(Const("word",_),n)),_) as tm ->
  snd (bm_seq_numeral tm (dest_numeral n))
| _ -> failwith "BITMATCH_CONV";;


(* Given a bitmatch term 'tm', 'bm_check_disjointness tm' checks whether there
   exist two bit patterns that overlap. Two bit patterns overlap if there
   exists at least one bitvector that can be matched to both of them. If there
   exists such overlapping patterns, 'bm_check_disjointness' throws
   Invalid_argument. This function is useful when you want to ensure that
   the bitmatch can be successfully handled by BITMATCH_CONV. *)
let bm_check_disjointness =
  let rec first_n l n = if n = 0 then [] else
    match l with | h::t -> h::(first_n t (n-1)) | [] -> [] in
  (* Do two patterns overlap? *)
  let overlaps (pat0: bool option array) pat1 sz =
    begin let overlaps_i idx =
      match pat0.(idx), pat1.(idx) with
      | Some b0, Some b1 -> b0 = b1
      | _, _ -> true (* always can assign bit(s) that make them equal *) in
    let rec overlaps_all idx =
      if idx = sz then true
      else (overlaps_i idx) && overlaps_all (idx+1) in
    overlaps_all 0 end in
  (* Given term tm, do the main check. *)
  fun tm -> match tm with
  | Comb(Comb(Const("_BITMATCH",_),bitval),patterns) ->
    let valty = type_of bitval in
    begin match valty with
    | Tyapp("word", [N]) ->
      let bitwidth = Num.int_of_num (dest_finty N) in
      let pattern_arrs = bm_analyze_clauses bitwidth patterns in

      List.iteri (fun idx0 pattern0 ->
        List.iteri (fun idx1 pattern1 ->
            if overlaps pattern0 pattern1 bitwidth then
              let idx0_str = string_of_int idx0 in
              let idx1_str = string_of_int idx1 in
              invalid_arg ("Pattern number " ^ idx0_str ^
                           " and pattern number " ^ idx1_str ^ " overlap")
            else ())
          (first_n pattern_arrs idx0))
        pattern_arrs
    | _ -> invalid_arg "bm_check_disjointness: word's bitwidth is unknown"
    end
  | _ -> invalid_arg "bm_check_disjointness: not bitmatch";;

(* Unit tests for bm_check_disjointness *)
let _ = bm_check_disjointness
    `bitmatch (x:(2)word) with | [0b00:2] -> T | [0b10:2] -> T`;;
let _ = bm_check_disjointness
    `bitmatch (x:(2)word) with | [T; x] -> T | [F; y] -> T`;;
let _ = try
    bm_check_disjointness
        `bitmatch (x:(2)word) with | [0b00:2] -> T | [0b00:2] -> T`;
    failwith "Must fail"
  with Invalid_argument _ -> ();;
let _ = try
    bm_check_disjointness
        `bitmatch (x:(2)word) with | [T; x] -> T | [y; T] -> T`;
    failwith "Must fail"
  with Invalid_argument _ -> ();;
let _ = try
    bm_check_disjointness
        `bitmatch (x:(2)word) with | [0b11:2] -> T | [0b00:2] -> T | [0b00:2] -> T`;
    failwith "Must fail"
  with Invalid_argument _ -> ();;
