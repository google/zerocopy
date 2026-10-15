(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Additional utilities that could be part of HOL Light libraries.           *)
(* ========================================================================= *)

prioritize_num();;

let rec dest_list = function
| Const("NIL",_) -> []
| Comb(Comb(Const("CONS",_),a),t) -> a :: dest_list t
| _ -> failwith "dest_list";;

let catch f x = try Some(f x) with Failure _ -> None;;

(* --------------------------------------------------------------------- *)
(* Compatibility shims for OCaml < 4.08 (Option module absent).          *)
(* --------------------------------------------------------------------- *)

let option_get = function Some x -> x | None -> failwith "option_get";;
let option_map f = function Some x -> Some (f x) | None -> None;;
let option_bind opt f = match opt with Some x -> f x | None -> None;;
let option_is_some = function Some _ -> true | None -> false;;

(* --------------------------------------------------------------------- *)
(* Compatibility for List.filter_map (not available before OCaml 4.08).  *)
(* --------------------------------------------------------------------- *)

let rec filter_map f = function
  | [] -> []
  | x :: xs ->
    match f x with
    | Some y -> y :: filter_map f xs
    | None -> filter_map f xs;;

(* --------------------------------------------------------------------- *)
(* Compatibility for String.starts_with/ends_with (OCaml < 4.13).        *)
(* --------------------------------------------------------------------- *)

let starts_with prefix s =
  let plen = String.length prefix in
  String.length s >= plen && String.sub s 0 plen = prefix;;

let ends_with suffix s =
  let slen = String.length suffix and len = String.length s in
  len >= slen && String.sub s (len - slen) slen = suffix;;

(* --------------------------------------------------------------------- *)
(* End of compatibility shims.                                            *)
(* --------------------------------------------------------------------- *)

let rec takedrop (n:int) (l:'a list): 'a list * 'a list =
  if n = 0 then ([],l)
  else
    match l with
    | [] -> failwith "l too short"
    | h::t ->
      let a,b = takedrop (n-1) t in
      (h::a,b);;

let pinst tyin tmin =
  let iterm_fn = vsubst (map (I F_F (inst tyin)) tmin)
  and itype_fn = inst tyin in
  fun th -> try iterm_fn (itype_fn th)
            with Failure _ -> failwith "pinst";;

let SPEC1_TAC = W (curry SPEC_TAC);;
let SPECL_TAC = EVERY o map SPEC1_TAC o rev;;

let (WITH_GOAL:(term->tactic)->tactic) = fun tac (_,w as st) -> tac w st;;

let CONV_RHS_RULE (conv:conv) th = TRANS th (conv (rhs (concl th)));;

let UNETA_TAC = function
| Comb(_,(Var(_,_) as x)) as t ->
  ONCE_REWRITE_TAC [SYM (ETA_CONV (mk_abs (x, t)))]
| _ -> failwith "UNETA_TAC";;

let rec REPEAT_MATCH_CONV ifif tm =
  try let th = MATCH_CONV tm in
      let tm' = rand(concl th) in
      if is_comb tm' && rator tm' = rator tm then
        TRANS th (REPEAT_MATCH_CONV ifif tm')
      else if is_cond tm' then
        let th' = (LAND_CONV (TRY_CONV MATCH_CONV) THENC
                   GEN_REWRITE_CONV TRY_CONV [ifif] THENC
                   RAND_CONV (REPEAT_MATCH_CONV ifif)) tm' in
        TRANS th th'
      else th
  with Failure _ -> REFL tm;;

let MATCH_CONV' =
  let ifif = prove
    (`(if p then if p then a:A else b else c) = if p then a else c`,
     COND_CASES_TAC THEN REWRITE_TAC []) in
  REPEAT_MATCH_CONV ifif;;

let NUM_DIVIDES_CONV = REWRITE_CONV [DIVIDES_MOD] THENC NUM_REDUCE_CONV;;

let FORALL_FUN_PAIR_THM = prove
 (`!P. (!f:A#B->C. P f) <=> (!g. P(\a. g (FST a) (SND a)))`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN
  GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV) [GSYM PAIR] THEN
  PURE_ASM_REWRITE_TAC[]);;

let OPTION_DISTINCT = prove_constructors_distinct option_RECURSION;;

let OPTION_INJ = prove_constructors_injective option_RECURSION;;

let is_some = define
  `is_some (NONE:A option) = F /\ !a:A. is_some (SOME a) = T`;;

parse_as_infix(">>=",(14,"right"));;
let obind = define `NONE >>= f = NONE /\ !a:A. SOME a >>= f = f a: B option`;;

let obind_eq_some = prove
 (`!ao f b. (ao >>= f) = SOME (b:B) <=> ?a:A. ao = SOME a /\ f a = SOME b`,
  MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC [obind; OPTION_DISTINCT; OPTION_INJ] THEN METIS_TAC []);;

let ODD_DOUBLE = prove (`!n. ~ODD (2 * n)`,
  REWRITE_TAC [NOT_ODD; EVEN_DOUBLE]);;

let EXP_2_NE_0 = prove
  (`~(2 EXP n = 0)`, REWRITE_TAC [EXP_EQ_0; ARITH_EQ]);;

let ONE_LE_EXP_2 = prove(`forall y. 1 <= 2 EXP y`,
  REWRITE_TAC[ARITH_RULE`1=SUC 0`;LE_SUC_LT] THEN
  REWRITE_TAC[ARITH_RULE`0 < x <=> ~(x = 0)`;EXP_2_NE_0]);;

let MOD_DIV_EQ_0 = prove
  (`~(n = 0) ==> (m MOD n) DIV n = 0`, DISCH_THEN (fun th ->
    IMP_REWRITE_TAC [th; DIV_EQ_0; MOD_LT_EQ]));;

let BIT0_0 = prove (`BIT0 0 = 0`, REWRITE_TAC [NUMERAL; ARITH_ZERO]);;
let BIT1_0 = prove (`BIT1 0 = 1`, REWRITE_TAC [NUMERAL]);;

let exists_list_split = prove
 (`!l n. n <= LENGTH (l:A list) ==> ?l1 l2. l = APPEND l1 l2 /\ LENGTH l1 = n`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH] THENL [
    REWRITE_TAC [LE; FORALL_UNWIND_THM2] THEN
    REPEAT (EXISTS_TAC `[]:A list`) THEN REWRITE_TAC [APPEND; LENGTH];
    INDUCT_TAC THENL [DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`[]:A list`; `CONS h t:A list`] THEN
      REWRITE_TAC [APPEND; LENGTH];
      POP_ASSUM (K (POP_ASSUM (fun th1 -> DISCH_THEN (fun th2 ->
        let th = MATCH_MP th1 (REWRITE_RULE [LE_SUC] th2) in
        REPEAT_TCL CHOOSE_THEN (fun th3 ->
          MAP_EVERY EXISTS_TAC [`CONS h l1:A list`; `l2:A list`] THEN
          REWRITE_TAC [th3; APPEND; LENGTH]) th))))]]);;

(* A drop in replacement for prove that uses the interactive tactic creation
   tools so that the goalstack is displayed if the proof is not complete. *)
let start(t,tac) = let _ = g t in e tac;;

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

(* ------------------------------------------------------------------------- *)
(* Conversion from numerals to list bool.                                    *)
(* ------------------------------------------------------------------------- *)

let from_bitlist = define
  `from_bitlist [] = 0 /\
   (!b t. from_bitlist (CONS b t) =
     if b then BIT1 (from_bitlist t) else BIT0 (from_bitlist t))`;;

let FROM_BITLIST_CLAUSES = prove
  (`from_bitlist [] = 0 /\
    (!t. from_bitlist (CONS T t) = BIT1 (from_bitlist t)) /\
    (!t. from_bitlist (CONS F t) = BIT0 (from_bitlist t))`,
  REWRITE_TAC[from_bitlist]);;

(* ------------------------------------------------------------------------- *)
(* Given a numeral n, returns an equivalent bitlist of the given length.     *)
(* For example:                                                              *)
(*   TO_BITLIST_CONV 5 `6` = |- 6 = from_bitlist [F; T; T; F; F]             *)
(* ------------------------------------------------------------------------- *)

let TO_BITLIST_CONV: int -> conv =
  let th0 = prove (`0 = from_bitlist []`, REWRITE_TAC[from_bitlist])
  and th1 = prove
    (`!t. 0 = from_bitlist t ==> 0 = from_bitlist (CONS F t)`,
    CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[from_bitlist; ARITH_ZERO; NUMERAL])
  and thb0 = prove
    (`!n t. NUMERAL n = from_bitlist t ==>
      NUMERAL (BIT0 n) = from_bitlist (CONS F t)`,
    REWRITE_TAC[NUMERAL] THEN MESON_TAC[from_bitlist])
  and thb1 = prove
    (`!n t. NUMERAL n = from_bitlist t ==>
      NUMERAL (BIT1 n) = from_bitlist (CONS T t)`,
    REWRITE_TAC[NUMERAL] THEN MESON_TAC[from_bitlist]) in
  let rec thz i =
    if i < 0 then failwith "TO_BITLIST_CONV: numeral out of range"
    else if i = 0 then th0
    else
      let thr = thz (i - 1) in
      let t = rand (snd (dest_eq (concl thr))) in
      MP (SPEC t th1) thr in
  let rec th i n =
    match n with
      Const("_0",_) -> thz i
    | Comb(Const("BIT0",_),n) ->
        let (thr:thm) = th (i - 1) n in
        let t = rand (snd (dest_eq (concl thr))) in
        MP (SPECL [n; t] thb0) thr
    | Comb(Const("BIT1",_),n) ->
        let thr = th (i - 1) n in
        let t = rand (snd (dest_eq (concl thr))) in
        MP (SPECL [n; t] thb1) thr
    | _ -> failwith "TO_BITLIST_CONV: malformed numeral" in
  fun i tm ->
    match tm with
      Comb(Const("NUMERAL",_),n) when is_numeral n -> th i n
    | _ -> failwith "TO_BITLIST_CONV";;

(* ------------------------------------------------------------------------- *)
(* A memoized bitmatch conversion written by Alexey Solovyev.                *)
(* ------------------------------------------------------------------------- *)

(** BITMATCH_CONV is slow because it needs to construct
    a discrimination tree every time BITMATCH_CONV is invoked.
    This conversion memoizes discrimination trees so it works
    much faster when it is called several times for the same bitmatch
    pattern. *)

let BITMATCH_MEMO_CONV =
  let tree_memo = Hashtbl.create 64 in
  function
  | Comb(Comb((Const("_BITMATCH",_) as e),(Comb(Const("word",ty), n_tm))),cs) ->
    let w_ty = snd (dest_fun_ty ty) in
    let size = Num.int_of_num (dest_finty (dest_word_ty w_ty)) in
    let tr =
      try Hashtbl.find tree_memo cs
      with Not_found ->
        let w_var = mk_var ("$w", w_ty) in
        let w_tm = list_mk_comb (e, [w_var; cs]) in
        let _, tr = bm_build_pos_tree w_tm in
        Hashtbl.add tree_memo cs tr;
        tr in
    let nn = dest_numeral n_tm in
    let n = Num.int_of_num nn in
    let arr = Array.init size (fun i -> Some (n land (1 lsl i) != 0)) in
    let th = hd (snd (snd (get_dt arr tr))) in
    begin try
      let ls, th' = inst_bitpat_numeral (hd (hyp th)) nn in
      PROVE_HYP th' (INST ls th)
    with Failure _ ->
      failwith (sprintf "BITMATCH_MEMO_CONV: match failed: 0x%x" (Num.int_of_num nn))
    end
  | _ -> failwith "BITMATCH_MEMO_CONV";;


(* ------------------------------------------------------------------------- *)
(* A term rewriter for extracting out a bitmatch subexpression and defining  *)
(* it as a new constant. This is useful when BITMATCH_MEMO_CONV does not work*)
(* well. When the bitmatch uses the matching input variable inside its body  *)
(* as well, BITMATCH_MEMO_CONV cannot work well because the body changes.    *)
(* For example,                                                              *)
(*  `bitmatch w with | [pattern] -> ...(w)... | [pattern] -> ...(w) | ...`   *)
(* if w is instantiated with `word 0x12345678`,                              *)
(* the result is                                                             *)
(*  `bitmatch (word 0x12345678) with | [pattern] -> ..(word 0x12345678) | ..`*)
(* This cannot hit the cache inside BITMATCH_MEMO_CONV unless `w` has exactly*)
(* been instantiated as the same value in the past.                          *)
(* ------------------------------------------------------------------------- *)

(** Given a term t,
    (1) Find the innermost bitmatch expression of t,
    (2) Replace the innermost bitmatch expression with a new temporarily named
        constant, and also create a definition between the constant and the
        bitmatch expression
    (3) create a conversion that takes "opaque_const const_word" and reduces
        it using a decision tree of bitmatch.
    Returns: Some (|-t=t', opaque_def, opaque_def arity,
                  |-opaque_def=bitmatch.., <conversion>) where t' is t with
        the innermost bitmatch replaced iwth the opaque definition.
**)
let conceal_bitmatch: term -> (thm * term * int * thm * conv) option =
  (* Find bitmatch that does not have another bitmatch as a subterm
     If found, return (the bitmatch, bitmatch's input variable).
  *)
  let rec find_bitmatch (t:term): (term*term) option =
    match t with
    | Var(_,_) -> None
    | Const(_,_) -> None
    | Abs(_,y) -> find_bitmatch y
    | Comb(x,y) -> begin
      let t1 = find_bitmatch x in
      if t1 <> None then t1 else
      let t2 = find_bitmatch y in
      if t2 <> None then t2 else
      match x with
      | Comb(Const("_BITMATCH", _), Var(_,_)) -> Some (t,rand x)
      | _ -> None
    end in
  let fast_bitmatch_id = ref 0 in
  fun t ->
    match find_bitmatch t with
    | None -> None (* No bitmatch found *)
    | Some (bm,bvar) -> begin
      (* Create a new opaque bitmatch definition *)
      let newname = "__opaque_bitmatch_" ^ (string_of_int !fast_bitmatch_id) in
      let _ = fast_bitmatch_id := !fast_bitmatch_id + 1 in

      (* Collect free variables. *)
      let the_freevars = frees bm in
      (* Position the first input parameter of bitmatch as the first argument
         of the new opaque constant. *)
      let the_freevars = filter (fun t -> t <> bvar) the_freevars in
      let args = bvar::the_freevars in
      let argtys = map type_of args in

      let newty = itlist mk_fun_ty argtys (type_of bm) in
      let newdef_lhs = list_mk_comb (mk_var(newname,newty),args) in
      let new_abbrev = new_definition(mk_eq(newdef_lhs, bm)) in

      (* Create a pos tree (decision tree) *)
      let _, tr = bm_build_pos_tree bm in

      let bitwidth = Num.int_of_num (dest_finty (dest_word_ty (type_of bvar))) in

      let new_reducer:conv = fun tm ->
        if not (is_comb tm) then failwith "not comb" else
        let c,args = strip_comb tm in
        match c,args with
        | Const(the_name,_), ((Comb(Const("word",ty),n_tm))::args')
            when the_name = newname ->
          let nn = dest_numeral n_tm in
          let n = dest_small_numeral n_tm in
          let arr = Array.init bitwidth (fun i -> Some (n land (1 lsl i) != 0)) in
          let th = hd (snd (snd (get_dt arr tr))) in
          begin try
            let ls, th' = inst_bitpat_numeral (hd (hyp th)) nn in
            (GEN_REWRITE_CONV I [new_abbrev] THENC
             GEN_REWRITE_CONV I [PROVE_HYP th' (INST ls th)]) tm
          with Failure _ ->
            failwith (sprintf "conceal_bitmatch: match failed: 0x%x" n)
          end
        | _ -> failwith "" in
      Some ((REWRITE_CONV[GSYM new_abbrev] t), mk_const(newname,[]),
            length args, new_abbrev, new_reducer)
    end;;

(* Examples:
  let Some (th,opaqueconst,arity,oth,reducer) = conceal_bitmatch (concl arm_logop);;

  Output:
    val th : thm =
      |- (forall opc N Rd Rn Rm.
              arm_logop opc N Rd Rn Rm =
              (bitmatch opc with
                [0:2] -> SOME ((if N then arm_BIC else arm_AND) Rd Rn Rm)
              | [1:2] -> SOME ((if N then arm_ORN else arm_ORR) Rd Rn Rm)
              | [2:2] -> SOME ((if N then arm_EON else arm_EOR) Rd Rn Rm)
              | [3:2] -> SOME ((if N then arm_BICS else arm_ANDS) Rd Rn Rm))) <=>
        (forall opc N Rd Rn Rm.
              arm_logop opc N Rd Rn Rm = __opaque_bitmatch_92 opc N Rd Rn Rm)
    val opaqueconst : term = `__opaque_bitmatch_92`
    val arity : int = 5
    val oth : thm =
      |- forall opc N Rd Rn Rm.
            __opaque_bitmatch_92 opc N Rd Rn Rm =
            (bitmatch opc with
              [0:2] -> SOME ((if N then arm_BIC else arm_AND) Rd Rn Rm)
            | [1:2] -> SOME ((if N then arm_ORN else arm_ORR) Rd Rn Rm)
            | [2:2] -> SOME ((if N then arm_EON else arm_EOR) Rd Rn Rm)
            | [3:2] -> SOME ((if N then arm_BICS else arm_ANDS) Rd Rn Rm))
    val reducer : conv = <fun> (* a conversion that reduces `__opaque_bitmatch_92 ..`. *)

  Other examples:
    conceal_bitmatch (concl arm_movop);;
    conceal_bitmatch (concl arm_lsvop);;
    conceal_bitmatch (concl decode_shift);;
    conceal_bitmatch (concl decode_extendtype);;
    conceal_bitmatch (concl decode);;
*)

(* ------------------------------------------------------------------------- *)
(* Find substring                                                            *)
(* ------------------------------------------------------------------------- *)

let find_substring str sub =
  let str_len = String.length str in
  let sub_len = String.length sub in

  let rec f_search pos =
    if pos + sub_len > str_len then
      None
    else if String.sub str pos sub_len = sub then
      Some pos
    else
      f_search (pos + 1)
  in
  f_search 0;;
